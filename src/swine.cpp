#include "swine.h"

#include "brute_force.h"
#include "preprocessor.h"
#include "exp_finder.h"
#include "term_evaluator.h"
#include "util.h"
#include "term.h"

#include <assert.h>
#include <limits>

#define log(msg) _log(config, msg)
#define debug(msg) _debug(config, msg)

namespace swine {

using namespace boost::multiprecision;
using namespace range_utils;

std::ostream& operator<<(std::ostream &s, const Swine::EvaluatedExponential &exp) {
    return s <<
           "abstract: exp(" <<
           exp.base <<
           ", " <<
           exp.exponent <<
           "); concrete: exp(" <<
           exp.base_val <<
           ", " <<
           exp.exponent_val <<
           ") = " <<
           exp.exp_expression_val;
}

std::ostream& operator<<(std::ostream &s, const Swine &swine) {
    return s << swine.get_solver();
}

Swine::Frame::Frame(z3::context &ctx): exps(ctx) {}

Swine::Swine(const Config &config, z3::context &ctx):
    config(config),
    ctx(ctx),
    solver(ctx),
    util(std::make_unique<Util>(ctx, this->config, this->stats)),
    preproc(std::make_unique<Preprocessor>(*util)),
    exp_finder(std::make_unique<ExpFinder>(*util)),
    model(ctx),
    common_base(0),
    input(util->top()) {
    solver.set("model", true);
    if (config.get_lemmas) {
        solver.set("unsat_core", true);
    }
    frames.emplace_back(ctx);
}

Swine::~Swine(){
    return;
}

void Swine::add_lemma(const z3::expr &t, const LemmaKind kind) {
    log(kind << " lemma:\n" << t);
    if (config.validate_unsat || config.get_lemmas) {
        frames.back().lemma_kinds.emplace(t.id(), kind);
        frames.back().lemmas.emplace(t.id(), t);
    }
    if (config.get_lemmas) {
        static unsigned int count {0};
        const auto assumption {ctx.bool_const(("assumption_" + std::to_string(count)).c_str())};
        ++count;
        frames.back().assumptions.emplace_back(assumption, t);
        solver.add(assumption == t);
    } else {
        solver.add(t);
    }
    switch (kind) {
    case LemmaKind::Interpolation: ++stats.interpolation_lemmas;
        break;
    case LemmaKind::Symmetry: ++stats.symmetry_lemmas;
        break;
    case LemmaKind::Prime: ++stats.prime_lemmas;
        break;
    case LemmaKind::Bounding: ++stats.bounding_lemmas;
        break;
    case LemmaKind::Monotonicity: ++stats.monotonicity_lemmas;
        break;
    case LemmaKind::Induction: ++stats.induction_lemmas;
        break;
    case LemmaKind::EIA_n: ++stats.eia_n_lemmas;
        break;
    default: throw std::invalid_argument("unknown lemma kind");
    }
}

z3::expr Swine::get_value(const z3::expr &exp) const {
    return model.eval(exp, true);
}

bool Swine::update_common_base(const z3::expr &expr) {
    common_base = 0;
    for (const z3::expr &t : utils::find(expr, [](const z3::expr &e){ return e.is_int(); })) {
        std::optional<Term> term{Term::try_parse(t)};
        if (!term) {
            log("Not a term: " << t);
            common_base = {};
            return false;
        }
        for(const z3::expr &v : term->variables | std::views::values) {
            if (utils::is_var(v)) {
                continue;
            }
            if (!utils::is_exp(v)) {
                log("Not a linear term: " << v << " in " << *term);
                common_base = {};
                return false;
            }
            if (!v.arg(0).is_numeral() || !utils::is_var(v.arg(1))) {
                log("Not a constant raised by a variable: " << v << " in " << *term);
                common_base = {};
                return false;
            }
            if (!utils::join_common_base(common_base, utils::value(v.arg(0)))) {
                return false;
            }
        }
    }
    return true;
}

void Swine::symmetry_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    if (!config.is_active(LemmaKind::Symmetry)) {
        return;
    }
    z3::expr_vector sym_lemmas{ctx};
    for (const auto &f: frames) {
        for (const auto &e: f.exps) {
            const auto ee {evaluate_exponential(e)};
            if (ee.base_val < 0) {
                base_symmetry_lemmas(e, sym_lemmas);
            }
            if (ee.exponent_val < 0) {
                exp_symmetry_lemmas(e, sym_lemmas);
            }
            if (ee.base_val < 0 && ee.exponent_val < 0) {
                const auto neg {util->make_exp(-ee.base, -ee.exponent)};
                base_symmetry_lemmas(neg, sym_lemmas);
                exp_symmetry_lemmas(neg, sym_lemmas);
            }
        }
    }
    for (const auto &l: sym_lemmas) {
        lemmas.emplace_back(l, LemmaKind::Symmetry);
    }
}

void Swine::base_symmetry_lemmas(const z3::expr &e, z3::expr_vector &lemmas) {
    if (!config.is_active(LemmaKind::Symmetry)) {
        return;
    }
    const auto base {e.arg(0)};
    const auto exp {e.arg(1)};
    if (!utils::is_value(base) || utils::value(base) < 0) {
        const auto conclusion_even {e == util->make_exp(-base, exp)};
        const auto conclusion_odd {e == -util->make_exp(-base, exp)};
        auto premise_even {z3::mod(exp, ctx.int_val(2)) == ctx.int_val(0)};
        auto premise_odd {z3::mod(exp, ctx.int_val(2)) == ctx.int_val(1)};
        lemmas.push_back(z3::implies(premise_even, conclusion_even));
        lemmas.push_back(z3::implies(premise_odd, conclusion_odd));
    }
}

void Swine::exp_symmetry_lemmas(const z3::expr &e, z3::expr_vector &lemmas) {
    if (!config.is_active(LemmaKind::Symmetry)) {
        return;
    }
    const auto base {e.arg(0)};
    const auto exp {e.arg(1)};
    const auto lemma {e == util->make_exp(base, -exp)};
    lemmas.push_back(lemma);
}

void Swine::compute_bounding_lemmas(const ExpGroup &g) {
    if (!config.is_active(LemmaKind::Bounding)) {
        return;
    }
    for (const auto &e: g.maybe_non_neg_base()) {
        auto [it, inserted] {frames.back().bounding_lemmas.emplace(e.id(), z3::expr_vector(ctx))};
        if (!inserted) {
            return;
        }
        auto &set {it->second};
        const auto base {e.arg(0)};
        const auto exp {e.arg(1)};
        z3::expr lemma{ctx};
        // exp = 0 ==> base^exp = 1
        lemma = z3::implies(exp == ctx.int_val(0), e == ctx.int_val(1));
        set.push_back(lemma);
        // exp = 1 ==> base^exp = base
        lemma = z3::implies(exp == ctx.int_val(1), e == base);
        set.push_back(lemma);
        if (!utils::is_value(base) || utils::value(base) == 0) {
            // base = 0 && ... ==> base^exp = 0
            lemma = (base == ctx.int_val(0) && exp != ctx.int_val(0)) == (e == ctx.int_val(0));
            set.push_back(lemma);
        }
        if (!utils::is_value(base) || utils::value(base) == 1) {
            // base = 1 && ... ==> base^exp = 1
            lemma = z3::implies(base == ctx.int_val(1), e == ctx.int_val(1));
            set.push_back(lemma);
        }
        if (!utils::is_value(base) || utils::value(base) > 1) {
            // exp + base > 4 && s > 1 && t > 1 ==> base^exp > s * t + 1
            lemma = z3::implies(
                base + exp > ctx.int_val(4) && base > ctx.int_val(1) && exp > ctx.int_val(1),
                e > base * exp + ctx.int_val(1));
            set.push_back(lemma);
        }
    }
}

void Swine::bounding_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    if (!config.is_active(LemmaKind::Bounding)) {
        return;
    }
    std::unordered_set<unsigned> seen;
    for (const auto &f: frames) {
        for (const auto &g: f.exp_groups) {
            if (seen.contains(g->orig().id())) {
                continue;
            }
            seen.emplace(g->orig().id());
            for (const auto &e: g->maybe_non_neg_base()) {
                const auto ee {evaluate_exponential(e)};
                if (ee.exp_expression_val != ee.expected_val && ee.base_val >= 0) {
                    for (const auto &l: f.bounding_lemmas.at(e.id())) {
                        lemmas.emplace_back(l, LemmaKind::Bounding);
                    }
                }
            }
        }
    }
}

void Swine::add(const z3::expr &t) {
    ++stats.num_assertions;
    log("assertion:\n" << t);
    input = input && t;
}

Swine::EvaluatedExponential::EvaluatedExponential(const z3::expr &exp_expression):
    exp_expression(exp_expression),
    base(exp_expression.arg(0)),
    exponent(exp_expression.arg(1)) {}

Swine::EvaluatedExponential Swine::evaluate_exponential(const z3::expr &exp_expression) const {
    EvaluatedExponential res{exp_expression};
    res.exp_expression_val = utils::value(get_value(res.exp_expression));
    res.base_val = utils::value(get_value(res.base));
    res.exponent_val = utils::to_int(get_value(res.exponent));
    res.expected_val = pow(res.base_val, abs(res.exponent_val));
    return res;
}

Swine::Interpolant::Interpolant(const z3::expr &t): t(t) {}

Swine::Interpolant Swine::interpolate(const z3::expr &t, const unsigned pos, const cpp_int x1, const cpp_int x2) {
    Interpolant res{t};
    z3::expr_vector children{ctx};
    for (const auto &c: t.args()) {
        children.push_back(c);
    }
    auto x {children[pos]};
    auto t1 {util->term(x1)};
    children.set(pos, t1);
    const auto at_x1 {t.decl()(children)};
    res.factor = abs(x2 - x1);
    if (res.factor == 0) {
        res.factor = 1;
        res.t = at_x1;
    } else {
        auto t2 = util->term(x2);
        children.set(pos, t2);
        const auto at_x2 {t.decl()(children)};
        res.t = util->term(res.factor) * at_x1 + (at_x2 - at_x1) * (x - util->term(x1));
    }
    return res;
}

z3::expr Swine::interpolation_lemma(const z3::expr &t, const bool upper, const std::pair<cpp_int, long long> a, const std::pair<cpp_int, long long> b) {
    const auto x1 {min(a.first, b.first)};
    const auto x2 {max(a.first, b.first)};
    const auto y1 {std::min(a.second, b.second)};
    const auto y2 {std::max(a.second, b.second)};
    const auto base {t.arg(0)};
    const auto exp {t.arg(1)};
    // const auto op = upper ? Le : Ge;
    // y1 <= exponent <= y2
    const auto exponent_in_bounds {util->term(y1) <= exp && exp <= util->term(y2)};
    // exponent > 0
    const auto exponent_positive {exp > util->term(0)};
    if (utils::is_value(base)) {
        const auto i {interpolate(t, 1, y1, y2)};
        const auto premise = upper ? exponent_in_bounds : exponent_positive;
        const auto conclusion_lhs {t * util->term(i.factor)};
        const auto conclusion = upper ? conclusion_lhs <= i.t : conclusion_lhs >= i.t;
        return z3::implies(premise, conclusion);
    } else {
        const auto at_y1 {util->make_exp(base, util->term(y1))};
        const auto at_y2 {util->make_exp(base, util->term(y2))};
        const auto i1 {interpolate(at_y1, 0, x1, x2)};
        const auto i2 {interpolate(at_y2, 0, x1, x2)};
        z3::expr premise{ctx};
        if (upper) {
            // x1 <= base <= x2
            const auto base_in_bounds {util->term(x1) <= base && base <= util->term(x2)};
            premise = base_in_bounds && exponent_in_bounds;
        } else {
            // exponent >= y1
            const auto exponent_above_threshold {exp >= util->term(y1)};
            // base > 0
            const auto base_positive {base > util->term(0)};
            premise = base_positive && exponent_above_threshold;
        }
        z3::expr conclusion {ctx};
        if (y2 == y1) {
            const auto lhs {t * util->term(i1.factor)};
            conclusion = upper ? lhs <= i1.t : lhs >= i1.t;
        } else {
            const auto y_diff {util->term(y2 - y1)};
            const auto lhs {t * util->term(i1.factor) * y_diff};
            const auto rhs {i1.t * y_diff + (i2.t - i1.t) * (exp - util->term(y1))};
            conclusion = upper ? lhs <= rhs : lhs >= rhs;
        }
        return z3::implies(premise, conclusion);
    }
}

void Swine::interpolation_lemma(const EvaluatedExponential &e, std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    z3::expr lemma{ctx};
    auto &vec {interpolation_points.emplace(e.exp_expression.id(), std::vector<std::pair<cpp_int, long long>>()).first->second};
    if (e.exp_expression_val < e.expected_val) {
        const auto min_base = e.base_val > 1 ? e.base_val - 1 : e.base_val;
        const auto min_exp = e.exponent_val > 1 ? e.exponent_val - 1 : e.exponent_val;
        lemma = interpolation_lemma(e.exp_expression, false, {min_base, min_exp}, {min_base + 1, min_exp + 1});
    } else {
        std::pair<cpp_int, long long> nearest {1, 1};
        auto min_dist {e.base_val * e.base_val + e.exponent_val * e.exponent_val};
        for (const auto &[x, y]: vec) {
            const auto x_dist {x - e.base_val};
            const auto y_dist {y - e.exponent_val};
            const auto dist {x_dist * x_dist + y_dist * y_dist};
            if (0 < dist && dist <= min_dist) {
                nearest = {x, y};
            }
        }
        lemma = interpolation_lemma(e.exp_expression, true, {e.base_val, e.exponent_val}, nearest);
    }
    vec.emplace_back(e.base_val, e.exponent_val);
    lemmas.emplace_back(lemma, LemmaKind::Interpolation);
}

void Swine::interpolation_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    if (!config.is_active(LemmaKind::Interpolation)) {
        return;
    }
    for (const auto &f: frames) {
        for (const auto &g: f.exp_groups) {
            for (const auto &e: g->maybe_non_neg_base()) {
                const auto ee {evaluate_exponential(e)};
                if (ee.exp_expression_val != ee.expected_val && ee.base_val > 0 && ee.exponent_val > 0) {
                    interpolation_lemma(ee, lemmas);
                }
            }
        }
    }
}

std::optional<z3::expr> Swine::induction_lemma(EvaluatedExponential e1, EvaluatedExponential e2) {
    if (e1.base_val != e2.base_val || e1.exponent_val < 2 || e2.exponent_val < 2 || e1.exponent_val == e2.exponent_val) {
        return {};
    }
    if (e1.exponent_val > e2.exponent_val) {
        const auto tmp {e1};
        e1 = e2;
        e2 = tmp;
    }
    const auto base_val {e1.base_val};
    const auto diff_val {e2.exponent_val - e1.exponent_val};
    if (pow(base_val, e2.exponent_val) - pow(base_val, e1.exponent_val) != pow(base_val, diff_val)) {
        const auto diff {util->term(diff_val)};
        const z3::expr premise{e1.base == e2.base && e2.exponent - e1.exponent == diff && e1.exponent >= 0};
        const z3::expr conclusion{e2.exp_expression == e1.exp_expression * z3::pw(e1.base, diff)};
        return z3::implies(premise, conclusion);
    } else {
        return {};
    }
}

void Swine::induction_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    if (!config.is_active(LemmaKind::Induction)) {
        return;
    }
    std::unordered_map<cpp_int, std::vector<EvaluatedExponential>> exps_by_base;
    for (const auto &f: frames) {
        for (const auto &g: f.exp_groups) {
            for (const auto e: g->maybe_non_neg_base()) {
                const auto eval {evaluate_exponential(e)};
                if (eval.base_val > 1) {
                    const auto it {exps_by_base.emplace(eval.base_val, std::vector<EvaluatedExponential>()).first};
                    it->second.emplace_back(eval);
                }
            }
        }
    }
    for (auto &[_,exps]: exps_by_base) {
        if (exps.size() > 1) {
            std::sort(exps.begin(), exps.end(), [](const auto &e1, const auto &e2) {
                return e1.exponent_val < e2.exponent_val;
            });
            for (auto it = exps.begin(); std::next(it) != exps.end(); ++it) {
                if (const auto lem {induction_lemma(*it, *std::next(it))}) {
                    lemmas.emplace_back(*lem, LemmaKind::Induction);
                }
            }
        }
    }
}

std::optional<z3::expr> Swine::monotonicity_lemma(const EvaluatedExponential &e1, const EvaluatedExponential &e2) {
    if ((e1.base_val > e2.base_val && e1.exponent_val < e2.exponent_val)
        || (e1.base_val < e2.base_val && e1.exponent_val > e2.exponent_val)
        || (e1.base_val == e2.base_val && e1.exponent_val == e2.exponent_val)) {
        return {};
    }
    bool is_smaller = e1.base_val < e2.base_val || e1.exponent_val < e2.exponent_val;
    const auto [smaller, greater] = is_smaller ? std::pair(e1, e2) : std::pair(e2, e1);
    if (smaller.exp_expression_val < greater.exp_expression_val) {
        return {};
    }
    z3::expr premise{ctx};
    const z3::expr strict_exp_premise {smaller.exponent < greater.exponent};
    const z3::expr non_strict_exp_premise {smaller.exponent <= greater.exponent};
    if (!utils::is_value(smaller.base) || !utils::is_value(greater.base)) {
        const z3::expr strict_base_premise {smaller.base < greater.base};
        const z3::expr non_strict_base_premise {smaller.base <= greater.base};
        premise = non_strict_base_premise && non_strict_exp_premise && (strict_base_premise || strict_exp_premise);
    } else if (smaller.base_val < greater.base_val) {
        premise = non_strict_exp_premise;
    } else {
        premise = strict_exp_premise;
    }
    premise = ctx.int_val(1) < smaller.base && ctx.int_val(0) < smaller.exponent && premise;
    return z3::implies(premise, smaller.exp_expression < greater.exp_expression);
}

void Swine::monotonicity_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    if (!config.is_active(LemmaKind::Monotonicity)) {
        return;
    }
    // search for pairs exp(b,e1), exp(b,e2) whose models violate monotonicity of exp
    z3::expr_vector exps{ctx};
    for (const auto &f: frames) {
        for (const auto &g: f.exp_groups) {
            for (const auto &e: g->maybe_non_neg_base()) {
                const auto base {e.arg(0)};
                const auto exp {e.arg(1)};
                if (utils::value(get_value(base)) > 1 && utils::value(get_value(exp)) > 0) {
                    exps.push_back(e);
                }
            }
        }
    }
    for (auto it1 = exps.begin(); it1 != exps.end(); ++it1) {
        const auto e1 {evaluate_exponential(*it1)};
        for (auto it2 = it1; ++it2 != exps.end();) {
            const auto e2 {evaluate_exponential(*it2)};
            const auto mon_lemma {monotonicity_lemma(e1, e2)};
            if (mon_lemma) {
                lemmas.emplace_back(*mon_lemma, LemmaKind::Monotonicity);
            }
        }
    }
}

void Swine::prime_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    if (!config.is_active(LemmaKind::Prime)) {
        return;
    }
    for (auto f: frames) {
        for (auto e: f.exps) {
            const auto ee {evaluate_exponential(e)};
            if (ee.exp_expression_val < 2 || ee.base_val < 2) {
                continue;
            }
            auto base_val {ee.base_val};
            auto val {ee.exp_expression_val};
            while (val % base_val == 0) {
                val /= base_val;
            }
            auto done {false};
            const auto process_divisor = [&](const auto &d) {
                if (val % d == 0 && base_val % d == 0) {
                    while (val % d == 0) {
                        val /= d;
                    }
                    while (base_val % d == 0) {
                        base_val /= d;
                    }
                } else {
                    const auto dt {util->term(d)};
                    const auto l {(z3::mod(ee.base, dt) == 0) == (z3::mod(ee.exp_expression, dt) == 0)};
                    lemmas.emplace_back(l, LemmaKind::Prime);
                    return true;
                }
                return false;
            };
            for (const auto d: std::vector{2,3,5}) {
                process_divisor(d);
            }
            if (done) {
                continue;
            }
            int inc[8] {4, 2, 4, 2, 4, 6, 2, 6};
            cpp_int d{7};
            auto i{0};
            while (d * d <= val) {
                process_divisor(d);
                d = d + inc[i];
                i = (i + 1) % 8;
            }
            if (!done) {
                const auto dt {util->term(base_val)};
                const auto l{(z3::mod(ee.base, dt) == 0) == (z3::mod(ee.exp_expression, dt) == 0)};
                lemmas.emplace_back(l, LemmaKind::Prime);
            }
        }
    }
}

void Swine::eia_n_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    if (!eia_proj || !config.is_active(LemmaKind::EIA_n)) {
        return;
    }
    const auto [premise, projected] = eia_proj->evaluateCase(solver.get_model());

    if(projected) {
        log("Projected to true -> no new EIA_" << *common_base << " lemmas");
//        ++util->stats.unusable_eia_n_lemmas;
        return;
    }

    assert(get_value(premise).is_true());
    log("Approximation projected formula to false, with premise:\n" << premise);

    lemmas.emplace_back(!premise, LemmaKind::EIA_n);
}

void Swine::add_bounds() {
    std::unordered_set<unsigned int> seen;
    const auto b {util->term(pow(cpp_int(2), bound))};
    for (const auto &f: frames) {
        for (const auto &g: f.exp_groups) {
            for (const auto &e: g->all()) {
                const auto exponent {e.arg(1)};
                if (seen.insert(exponent.id()).second) {
                    solver.add(exponent <= b);
                    solver.add(-b <= exponent);
                }
            }
        }
    }
}

std::vector<std::pair<z3::expr, LemmaKind>> Swine::preprocess_lemmas(const std::vector<std::pair<z3::expr, LemmaKind>> &lemmas) {
    std::vector<std::pair<z3::expr, LemmaKind>> res;
    for (const auto &[l,k]: lemmas) {
        const auto p {preproc->preprocess(l, false)};
        if (get_value(p).is_false()) {
            res.emplace_back(p, k);
        }
    }
    return res;
}

z3::check_result Swine::check(z3::expr_vector assumptions) {
    const bool eia_n{config.is_active(LemmaKind::EIA_n)};
    try {
        z3::expr formula{ctx};
        if (config.is_active(LemmaKind::EIA_n)) {
            formula = preproc->preprocess(input, true);
            if (update_common_base(formula)) {
                log("Using exponent substitutions");
                util->base = *common_base;
                eia_proj = std::make_unique<EIAProj>(*util, formula);
            } else {
                log("Restarting preprocessing");
                formula = preproc->preprocess(input, false);
            }
        } else {
            formula = preproc->preprocess(input, false);
        }
        solver.add(formula);

        frames.back().preprocessed_assertions.clear();
        if (config.validate_sat || config.validate_unsat || config.get_lemmas) {
            frames.back().preprocessed_assertions.emplace_back(formula, input);
        }
        frames.back().exp_ids.clear();
        frames.back().exps.resize(0);
        frames.back().exp_groups.clear();
        stats.non_constant_base = true;
        for (const auto &g: exp_finder->find_exps(formula)) {
            if (frames.back().exp_ids.emplace(g.orig().id()).second) {
                frames.back().exps.push_back(g.orig());
                frames.back().exp_groups.emplace_back(std::make_shared<ExpGroup>(g));
                stats.non_constant_base |= !g.has_ground_base();
                compute_bounding_lemmas(g);
            }
        }
    } catch (const ExponentOverflow &e) {
        frames.back().assert_failed = true;
        return z3::unknown;
    }

    z3::check_result res {z3::unknown};
    if (eia_n && common_base && !*common_base) {
        std::cout << ": Z3     ";
        res = check_with_z3(assumptions);
    } else if (!eia_n || !common_base || config.model) {
        std::cout << ": Lemmas ";
        res = check_with_lemmas(assumptions);
    } else if (config.non_lazy) {
        std::cout << ": EIA    ";
        res = check_with_eia_n(assumptions);
    } else {
        std::cout << ": EIAProj";
        res = check_with_eia_n_proj(assumptions);
    }
    return res;
}

z3::check_result Swine::check_with_z3(const z3::expr_vector &assumptions) {
    const z3::check_result res {assumptions.empty() ? solver.check() : solver.check(assumptions)};
    if (res == z3::sat && config.validate_sat) {
        verify();
    } else if(res == z3::unsat && config.validate_unsat) {
        brute_force();
    }
    return res;
}

z3::check_result Swine::check_with_eia_n(const z3::expr_vector &assumptions) {
//    return EIANSolver(*util).check((assumptions | rangify | util->reduce_and()) && (solver.assertions() | rangify | util->reduce_and()));
    return z3::unknown;
}

z3::check_result Swine::check_with_eia_n_proj(const z3::expr_vector &assumptions) {
    z3::check_result res = z3::unknown;

    for(unsigned int iterations = 1; config.rlimit == 0 || config.rlimit <= iterations; iterations++) {

        ++util->stats.iterations;
        log("---------------- Approximation iteration #" << iterations << " ----------------");

        Timer timer;
        res = solver.check(assumptions);
//        util->stats.timings.approximate += timer;
        if(res != z3::sat) {
            assert(res == z3::unsat);
            log("No approximation found -> unsat after " << iterations << " iteration" << (iterations == 1 ? "" : "s"));
            break;
        }

        log("Approximation:\n" << solver.get_model());
        const auto [premise, projected] = eia_proj->evaluateCase(solver.get_model());

        if(projected) {
            log("Projected to true -> sat after " << iterations << (iterations == 1 ? " iteration" : " iterations"));
            res = z3::sat;
            break;
        }
        assert(get_value(premise).is_true());
        log("Approximation projected formula to false, with premise:\n" << premise);
        ++util->stats.eia_n_lemmas;
        solver.add(!premise);
    }

    if(res == z3::sat && config.validate_sat) {
        std::cout << "\nVerify not applicable for EIAProj algorithm" << std::endl;
    }
    else if (res == z3::unsat && config.validate_unsat) {
        brute_force();
    }
    return res;
}

z3::check_result Swine::check_with_lemmas(z3::expr_vector &assumptions) {
    try {
        frames.back().exp_ids.clear();
        frames.back().exps.resize(0);
        frames.back().exp_groups.clear();
        stats.non_constant_base = true;
        for (const auto &g: exp_finder->find_exps(solver.assertions() | rangify | util->reduce_and())) {
            if (frames.back().exp_ids.emplace(g.orig().id()).second) {
                frames.back().exps.push_back(g.orig());
                frames.back().exp_groups.emplace_back(std::make_shared<ExpGroup>(g));
                stats.non_constant_base |= !g.has_ground_base();
                compute_bounding_lemmas(g);
            }
        }
    } catch (const ExponentOverflow &e) {
        frames.back().assert_failed = true;
        return z3::unknown;
    }

    auto res {z3::unknown};
    unsigned rconsumption {0};
    while (config.rlimit == 0 || rconsumption < config.rlimit) {
        try {
            ++rconsumption;
            ++stats.iterations;
            if (config.get_lemmas) {
                for (const auto &f: frames) {
                    for (const auto &[a,_]: f.assumptions) {
                        assumptions.push_back(a);
                    }
                }
            }
            if (config.toggle_mode && sat_mode) {
                solver.push();
                add_bounds();
            }
            if (!assumptions.empty()) {
                res = solver.check(assumptions);
            } else {
                res = solver.check();
            }
            if (res == z3::unsat) {
                if (config.toggle_mode && sat_mode) {
                    sat_mode = false;
                    solver.pop();
                    continue;
                }
                if (config.get_lemmas) {
                    const auto core {solver.unsat_core()};
                    std::unordered_set<unsigned> ids;
                    for (const auto &c: core) {
                        ids.insert(c.id());
                    }
                    std::cout << "===== lemmas =====" << std::endl;
                    for (const auto &k: lemma_kind::values) {
                        auto first {true};
                        for (const auto &f: frames) {
                            for (const auto &[a,l]: f.assumptions) {
                                if (ids.contains(a.id()) && f.lemma_kinds.at(l.id()) == k) {
                                    if (first) {
                                        std::cout << "----- " << k << " lemmas -----" << std::endl;
                                        first = false;
                                    }
                                    std::cout << l << std::endl;
                                }
                            }
                        }
                    }
                }
                if (config.validate_unsat) {
                    brute_force();
                }
                break;
            } else if (res == z3::unknown) {
                log("unknown from z3");
                break;
            } else if (res == z3::sat) {
                if (config.toggle_mode && !sat_mode) {
                    sat_mode = true;
                    ++bound;
                    continue;
                }
                model = solver.get_model();
                if (config.toggle_mode) {
                    solver.pop();
                }
                bool sat {true};
                log("candidate model:\n" << model);
                std::vector<std::pair<z3::expr, LemmaKind>> lemmas;
                // check if the model can be lifted
                for (const auto &f: frames) {
                    for (const auto &e: f.exps) {
                        const auto ee {evaluate_exponential(e)};
                        if (ee.exp_expression_val != ee.expected_val) {
                            sat = false;
                            break;
                        }
                    }
                    if (!sat) {
                        break;
                    }
                }
                if (sat) {
                    if (config.validate_sat) {
                        verify();
                    }
                    if (config.get_lemmas) {
                        std::cout << "===== lemmas =====" << std::endl;
                        for (const auto &k: lemma_kind::values) {
                            auto first {true};
                            for (const auto &f: frames) {
                                for (const auto &[id,l]: f.lemmas) {
                                    if (f.lemma_kinds.at(id) == k) {
                                        if (first) {
                                            std::cout << "----- " << k << " lemmas -----" << std::endl;
                                            first = false;
                                        }
                                        std::cout << l << std::endl;
                                    }
                                }
                            }
                        }
                    }
                    break;
                }
                symmetry_lemmas(lemmas);
                lemmas = preprocess_lemmas(lemmas);
                if (lemmas.empty()) {
                    bounding_lemmas(lemmas);
                    lemmas = preprocess_lemmas(lemmas);
                }
                if (lemmas.empty()) {
                    monotonicity_lemmas(lemmas);
                    lemmas = preprocess_lemmas(lemmas);
                }
                if (lemmas.empty()) {
                    eia_n_lemmas(lemmas);
                    lemmas = preprocess_lemmas(lemmas);
                }
                if (lemmas.empty()) {
                    prime_lemmas(lemmas);
                    induction_lemmas(lemmas);
                    interpolation_lemmas(lemmas);
                    lemmas = preprocess_lemmas(lemmas);
                }
                if (lemmas.empty()) {
                    if (config.is_active(LemmaKind::Interpolation)) {
                        throw std::logic_error("refinement failed, but interpolation is enabled");
                    } else {
                        return z3::unknown;
                    }
                }
                for (const auto &[l, kind]: lemmas) {
                    add_lemma(l, kind);
                }
            }
        } catch (const ExponentOverflow &e) {
            return z3::unknown;
        }
    }
    return res;
}

z3::check_result Swine::check() {
    return check(z3::expr_vector(ctx));
}

void Swine::push() {
    solver.push();
    frames.emplace_back(ctx);
}

void Swine::pop() {
    solver.pop();
    frames.pop_back();
}

void Swine::reset() {
    solver.reset();
    frames.clear();
    frames.emplace_back(ctx);
    stats.reset();
    common_base = 0;
}

void Swine::verify() const {
    TermEvaluator eval{*util};
    const auto model {this->model};
    for (const auto &f: frames) {
        for (const auto &[_,a]: f.preprocessed_assertions) {
            if (!eval.evaluate(a, model).is_true()) {
                std::cout << "Validation of the following assertion failed:" << std::endl;
                std::cout << a << std::endl;
                std::cout << "model:" << std::endl;
                std::cout << model << std::endl;
                return;
            }
        }
    }
}

void Swine::brute_force() {
    z3::expr_vector assertions{ctx};
    for (const auto &f: frames) {
        for (const auto &[a,_]: f.preprocessed_assertions) {
            assertions.push_back(a);
        }
    }
    z3::expr_vector exps{ctx};
    for (const auto &f: frames) {
        for (const auto &e: f.exps) {
            exps.push_back(e);
        }
    }
    BruteForce bf(*util, assertions, exps);
    if (bf.check_sat()) {
        std::cout << "sat via brute force" << std::endl;
        log("candidate model:\n" << solver.get_model());
        for (const auto &f: frames) {
            for (const auto &[id,l]: f.lemmas) {
                if (!get_value(l).is_true()) {
                    std::cout << "violated " << f.lemma_kinds.at(id) << " lemma" << std::endl;
                    std::cout << l << std::endl;
                }
            }
        }
        verify();
    }
}

z3::context& Swine::get_ctx() {
    return ctx;
}

z3::func_decl& Swine::get_exp() {
    return *util->exp;
}

const z3::solver& Swine::get_solver() const {
    return solver;
}

const Statistics &Swine::get_stats() const {
    return stats;
}

z3::solver& Swine::get_solver() {
    return solver;
}

z3::model Swine::get_model() const {
    return solver.get_model();
}

}
