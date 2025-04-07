#include "util.h"
#include "term.h"

namespace swine {

using namespace range_utils;

bool expr_set::add(const z3::expr &expr) {
    auto [_,is_new] = emplace(expr.id(), expr);
    return is_new;
}

bool expr_set::erase(const z3::expr &expr) {
    return erase(expr.id());
}

bool expr_set::erase(unsigned int id) {
    return unordered_map<unsigned int, z3::expr>::erase(id);
}

bool expr_set::contains(const z3::expr &expr) {
    return contains(expr.id());
}

bool expr_set::contains(unsigned int expr_id) {
    return unordered_map<unsigned int, z3::expr>::contains(expr_id);
}

std::ostream& operator<<(std::ostream &s, const expr_set &set) {
    s << "{";
    bool first = true;
    for(const auto &[_,e] : set) {
        if(first)
            s << " " << e;
        else s << ", " << e;
        first = false;
    }
    return s << " }";
}

std::ostream& operator<<(std::ostream &s, const std::vector<z3::expr> &vec) {
    s << "[";
    bool first = true;
    for(const auto &e : vec) {
        if(first)
            s << " " << e;
        else s << ", " << e;
        first = false;
    }
    return s << " ]";
}


namespace utils {

    cpp_int value(const z3::expr &term) {
        return cpp_int(term.get_decimal_string(0));
    }

    cpp_int value(const z3::expr &term, const z3::model &interpretation) {
        return value(interpretation.eval(term, true));
    }

    long long to_int(const z3::expr &t) {
        try {
            return stoll(t.get_decimal_string(0));
        } catch (const std::out_of_range &e) {
            throw ExponentOverflow(t);
        }
    }

    bool is_value(const z3::expr &t) {
        return t.is_const() && t.decl().decl_kind() != Z3_OP_UNINTERPRETED;
    }

    bool is_uninterpreted(const z3::expr &expr, bool vars, bool functions) {
        if(!expr.is_app() || expr.decl().decl_kind() != Z3_OP_UNINTERPRETED)
            return false;
        return expr.num_args() == 0 ? vars : functions;
    }

    bool is_var(const z3::expr &expr) {
        return is_uninterpreted(expr, true, false);
    }

    bool is_var_or_func(const z3::expr &expr) {
        return is_uninterpreted(expr, true, true);
    }

    bool is_func(const z3::expr &expr) {
        return is_uninterpreted(expr, false, true);
    }

    bool is_exp(const z3::expr &e) {
        return is_func(e) && e.num_args() == 2 && e.decl().name().str() == "exp";
    }

    z3::expr term(const cpp_int &value, const z3::expr &ctx) {
        return ctx.ctx().int_val(value.str().c_str());
    }

    bool contains(const z3::expr &might_contain, const z3::expr &might_be_contained) {
        if(might_contain.id() == might_be_contained.id())
            return true;
        if(might_contain.is_app())
            for(unsigned int i=0; i<might_contain.num_args(); i++)
                if(contains(might_contain.arg(i), might_be_contained))
                    return true;
        return false;
    }

    void collect_vars(const z3::expr &expr, expr_set &into, bool vars, bool functions) {
        if(is_uninterpreted(expr, vars, functions))
            into.add(expr);
        for(unsigned int i=0; i<expr.num_args(); ++i)
            collect_vars(expr.arg(i), into, vars, functions);
    }

    expr_set variables_in(const z3::expr &expr, bool vars, bool functions) {
        return find(expr, [=](const z3::expr &e){ return is_uninterpreted(e, vars, functions); },   functions) | range_utils::to<expr_set>();
    }

    std::vector<z3::expr> find_where(const z3::expr &expr, const std::function<bool(const z3::expr &)> &predicate, const std::function<bool(const z3::expr &, bool)> &recurse) {
        return find_values_where<z3::expr>(
                expr,
                [&](const z3::expr &e){ return predicate(e) ? std::optional<z3::expr>(e) : std::optional<z3::expr>(); },
                [&](z3::expr e, std::optional<z3::expr> r){ return recurse(e, r.has_value()); }
        );
    }

    std::vector<z3::expr> find(const z3::expr &expr, const std::function<bool(const z3::expr &)> &predicate, bool search_in_success, bool search_in_failed) {
        return find_where(expr, predicate, [&](auto _, auto r){ return r ? search_in_success : search_in_failed; });
    }

    std::vector<z3::expr> find_bools(const z3::expr &expr, const std::function<bool(const z3::expr &)> &predicate, bool search_in_success, bool search_in_failed) {
        return find_where(
                expr,
                [&](auto e){ return e.is_bool() && predicate(e); },
                [&](auto e, auto r){ return e.is_bool() && (r ? search_in_success : search_in_failed); }
        );
    }

    z3::expr substitute(const z3::expr &expr, const z3::expr &to_be_replaced, const z3::expr &replacement) {
        z3::ast_vector_tpl<z3::expr> src { expr.ctx() };
        z3::ast_vector_tpl<z3::expr> dst { expr.ctx() };
        src.push_back(to_be_replaced);
        dst.push_back(replacement);
        z3::expr copy = expr;
        return copy.substitute(src, dst);
    }

    z3::expr substitute_ite_here(const z3::expr &expr, const z3::expr &ite, int depth) {
        return (ite.arg(0) && substitute(expr, ite, ite.arg(1)))
            || (!ite.arg(0) && substitute(expr, ite, ite.arg(2)));
    }

    z3::expr replace_ite(const z3::expr &expr) {
        if(!expr.is_bool())
            throw z3::exception("Cannot replace ITEs in terms directly");
        if(!expr.is_app() || expr.is_const())
            return expr;

        // Replace ITEs from outside to inside, to avoid creating new different ITEs

        z3::expr res = expr;
        while(true) {

            const expr_set topLevelITEs = find(res, [](const z3::expr &e){ return e.is_ite(); }) | to<expr_set>();
            if(topLevelITEs.empty())
                return res;

            std::unordered_map<unsigned int, size_t> containedITEs;
            for(const auto &[id,it] : topLevelITEs)
                containedITEs.emplace(id, (find(it, [](const z3::expr &e){ return e.is_ite(); }, true) | range_utils::to<expr_set>()).size() - 1);

            unsigned int maxID = containedITEs.begin()->first;
            for(const auto &[id, count] : containedITEs)
                if(count > containedITEs.at(maxID))
                    maxID = id;

            const z3::expr &ite = topLevelITEs.at(maxID);
            if(ite.arg(1).id() == ite.arg(2).id())
                res = substitute(res, ite, ite.arg(1));
            else res = substitute_ite_here(res, ite, 0);

            if(topLevelITEs.size() == 1 && containedITEs.at(maxID) == 0)
                return res;
        }
    }

    z3::expr inline_constants(const z3::expr &expr) {

        // Reused each iteration
        std::vector<std::pair<z3::expr, z3::expr>> replacements;
        // Inlined variables
        expr_set replaced;
        // Values of the inlined variables
        std::unordered_map<unsigned int, cpp_int> values;

        // Repeat to perform transitive inlining, e.g. (x = 1 && y = x + 1 && exp(y,z) > 2)
        z3::expr res = expr;
        while(true) {
            replacements.clear();

            // Only recurse along ANDs - ORs or NOTs don't necessarily need to be true in the final formula, so we don't
            // to inline them. We first select equalities and ANDs (and use in_success=True, in_failed=False to search exactly
            // there), then discard the ANDs.
            for(const z3::expr &eq: find_bools(res, [](const z3::expr &e) { return e.is_and() || (e.is_eq() && e.arg(0).is_int()); }, true, false)) {

                if(!eq.is_eq())
                    continue;

                std::optional<Term> lhs = Term::try_parse(eq.arg(0));
                if(!lhs) continue;
                std::optional<Term> rhs = Term::try_parse(eq.arg(1));
                if(!rhs) continue;

                // Subtract first, then check variable count: some terms may cancel out
                Term &t = *lhs;
                t.subtract(*rhs);
                if(t.variables.empty() && t.constant != 0)
                    // c = 0 with c != 0 -> unsatisfiable
                    return eq.ctx().bool_val(false);
                if(t.variables.size() != 1)
                    continue;

                // Looking for (x - c = 0) <==> (n*x - n*c = 0)
                const auto &[coeff, var] = t.var_sum().front();
                if(!is_var(var))
                    continue;
                if(t.constant % coeff != 0)
                    // Unsatisfiable with ints
                    return eq.ctx().bool_val(false);

                // (n*x + c = 0) <==> (x = -c / n) (with (n | c) already checked)
                const cpp_int value = -t.constant / coeff;

                if(!values.contains(var.id())) {
                    values.emplace(var.id(), value);
                    replaced.add(var);
                    replacements.push_back({var, term(value, var)});
                }
                else if(values.at(var.id()) != value)
                    // Conflicting values for the same variable (e.g. (x == 1 && x == 2)) -> expression is false
                    return eq.ctx().bool_val(false);

                // Remove equality aka replace it with "true"
                replacements.push_back({eq, eq.ctx().bool_val(true)});
            }

            // No more variables to inline
            if(replacements.empty()) {
                if(!replaced.empty()) {
                    // Add x_i = c_i for each inlined variable; otherwise Z3 won't include them in a potential model
                    res = res && replaced
                                 | std::views::values
                                 | std::views::transform([&](const z3::expr &v) { return v == term(values.at(v.id()), v); })
                                 | reduce_and(expr);
                }
                return res;
            }

            // Actually perform inlining
            res = substitute_all(res, replacements);
        }
    }

    logic_reduction<true> reduce_and(const z3::expr &ctx) {
        return { ctx.ctx() };
    }

    logic_reduction<false> reduce_or(const z3::expr &ctx) {
        return { ctx.ctx() };
    }

    int cmp_in_interp(const z3::model &interpretation, const z3::expr &a, const z3::expr &b) {
        const cpp_int aVal = value(interpretation.eval(a));
        const cpp_int bVal = value(interpretation.eval(b));
        auto rel = aVal.compare(bVal);
        if(rel)
        return rel;
        return a.to_string().compare(b.to_string());
    }

    cpp_int floor_log(const cpp_int &x, const cpp_int &base) {
        cpp_int remaining = x;
        cpp_int log = 0;
        while(remaining /= base)
            ++log;
        return log;
    }

    cpp_int ceil_log(const cpp_int &x, const cpp_int &base) {
        return x == 1 ? 0 : floor_log(base, x - 1) + 1;
    }

    std::optional<cpp_int> log_exact(const cpp_int &base, const cpp_int &x) {
        cpp_int log = floor_log(base, x);
        if(abs_pow(base, log) == x)
            return log;
        else return { };
    }

    cpp_int abs_pow(const cpp_int &base, const cpp_int &exp) {
        cpp_int e = exp;
        if(e < 0)
            e = -e;

        if(e > std::numeric_limits<long long>().max())
            throw std::out_of_range(e.str());
        long long smallE = static_cast<long long>(e);

        if(base == 2)
            return (cpp_int) 1 << smallE;
        return boost::multiprecision::pow(base, smallE);
    }

    bool join_common_base(std::optional<cpp_int> &base, const std::optional<cpp_int> &base2) {
        if(!base || !base2) {
            base = { };
            return false;
        }
        if(!*base2)
            return true;
        if(!*base) {
            base = base2;
            return true;
        }
        if(*base == *base2)
            return true;
        base = {};
        return false;
    }
}



ExponentOverflow::ExponentOverflow(const z3::expr &t): std::out_of_range(""), t(t) {}

Util::Util(z3::context &ctx, const Config &config, Statistics &stats):
    config(config),
    stats(stats),
    ctx(ctx) {
    z3::sort_vector domain {ctx};
    domain.push_back(ctx.int_sort());
    domain.push_back(ctx.int_sort());
    exp = std::make_unique<z3::func_decl>(ctx.function("exp", domain, ctx.int_sort()));
}

z3::expr ExponentOverflow::get_t() const {
    return t;
}

z3::expr Util::term(const cpp_int &value) const {
    return ctx.int_val(value.str().c_str());
}

z3::expr Util::make_exp(const z3::expr &base, const z3::expr &exponent) const {
    return (*exp)(base, exponent);
}

z3::expr Util::make_exp(const z3::expr &exponent) const {
    assert(base);
    return (*exp)(term(base), exponent);
}

z3::expr Util::bool_expr(const bool value) const {
    return ctx.bool_val(value);
};

z3::expr Util::top() const {
    return bool_expr(true);
}

z3::expr Util::bot() const {
    return bool_expr(false);
}

z3::expr Util::new_variable() {
    return ctx.constant(new_symbol(), ctx.int_sort());
}

z3::symbol Util::new_symbol() {
    // Z3 doesn't seem to have a concept of "fresh variables" / symbols, at least it's not exposing it.
    // Thus, we choose a cryptic variable name and append an incrementing number.
    return ctx.str_symbol(("__var" + std::to_string(var_counter++)).c_str());
}

logic_reduction<true> Util::reduce_and() const {
    return utils::reduce_and(ctx);
}

logic_reduction<false> Util::reduce_or() const {
    return utils::reduce_or(ctx);
}

cpp_int Util::floor_log(const cpp_int &x) const {
    assert(base);
    return utils::floor_log(base, x);
}

cpp_int Util::ceil_log(const cpp_int &x) const {
    assert(base);
    return utils::ceil_log(base, x);
}

std::optional<cpp_int> Util::log_exact(const cpp_int &x) const {
    return utils::log_exact(base, x);
}

cpp_int Util::abs_pow(const cpp_int &exponent) const {
    assert(base);
    return utils::abs_pow(base, exponent);
}

}
