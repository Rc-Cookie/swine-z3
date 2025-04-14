#include "preprocessor.h"
#include "config.h"
#include "comparison.h"

#define write_log(msg) _log(util.config, msg)
#define write_debug(msg) _debug(util.config, msg)

namespace swine {

using namespace range_utils;
using namespace std::views;

Preprocessor::Preprocessor(Util &util): util(util), rewriter(util), constant_propagator(util) {}

PreprocResult Preprocessor::preprocess(const z3::expr &term, bool full) {
    const auto log = [&](const z3::expr &term, const PreprocKind kind, const std::function<z3::expr(const z3::expr&)> &f){
        bool done {false};
        const z3::expr res {f(term)};
        if ((util.config.log || util.config.debug) && res.id() != term.id()) {
            std::cout << kind << ":" << std::endl;
            std::cout << res << std::endl;
        }
        return res;
    };
    const std::function<z3::expr(const z3::expr&)> cp {[&](const z3::expr &term) {
            return constant_propagator.propagate(term);
        }
    };
    const std::function<z3::expr(const z3::expr&)> rw {[&](const z3::expr &term) {
            return rewriter.rewrite(term);
        }
    };
    const std::function<z3::expr(const z3::expr&)> do_cp {[&](const z3::expr &term) {
            if (util.config.is_active(PreprocKind::ConstantFolding)) {
                return log(term, PreprocKind::ConstantFolding, cp);
            } else {
                return term;
            }
        }
    };
    const std::function<z3::expr(const z3::expr&)> do_rw {[&](const z3::expr &term) {
            if (util.config.is_active(PreprocKind::Rewriting)) {
                return log(term, PreprocKind::Rewriting, rw);
            } else {
                return term;
            }
        }
    };
    write_log("preprocessing:\n" << term);
    auto last {term};
    auto cterm {do_cp(last)};
    auto rterm {do_rw(cterm)};
    auto res {rterm};
    while (res.id() != last.id()) {
        last = res;
        if (res.id() != cterm.id()) {
            cterm = do_cp(res);
            res = cterm;
        }
        if (res.id() != rterm.id()) {
            rterm = do_rw(res);
            res = rterm;
        }
    }

    res = res.simplify();
    write_log("simplify:\n" << res);
    if (!full || !util.config.is_active(LemmaKind::EIA_n)) {
        return { res, res, { } };
    }
    z3::expr simple = res;

    if (util.config.is_active(PreprocKind::Inlining)) {
        last = res;
        res = log(res, PreprocKind::Inlining, [&](const z3::expr &e){ return utils::inline_constants(e, util.config.model || util.config.validate_sat); });
        if (res.id() != last.id()) {
            res = res.simplify();
            write_log("simplify:\n" << res);
        }
        while (res.id() != last.id()) {
            last = res;
            if (res.id() != cterm.id()) {
                cterm = do_cp(res);
                res = cterm;
            }
            if (res.id() != rterm.id()) {
                rterm = do_rw(res);
                res = rterm;
            }
        }
    }

    std::optional<cpp_int> common_base = utils::get_eia_n_base(res);
    if (!common_base) {
        write_log("Not in EIA_n, no further preprocessing");
        return { simple, res, { } };
    }
    write_log("Formula in EIA_" << *common_base << ", further preprocessing");

    res = utils::replace_ite(res);
    write_log("replace ITEs:\n" << res);

    // Create variables for exponents that are not just a variable
    while(true) {
        const expr_set toBeSubstituted = utils::find(res, [](const z3::expr &e){ return utils::is_exp(e) && !utils::is_var(e.arg(1)); })
                                         | std::views::transform([](const z3::expr &exp){ return exp.arg(1); })
                                         | to<expr_set>();
        if(toBeSubstituted.empty())
            break;

        write_log("Introducing " << toBeSubstituted.size() << " variable" << (toBeSubstituted.size() == 1 ? "" : "s") << " for terms in exponents");

        std::vector<std::pair<z3::expr, z3::expr>> replacements = toBeSubstituted
                                                                  | std::views::values
                                                                  | std::views::transform([&](const z3::expr &e) -> std::pair<z3::expr, z3::expr> { return { e, util.new_variable() }; })
                                                                  | to_pairs<z3::expr>();
        z3::expr constraints = replacements
                               | std::views::transform([](const std::pair<z3::expr, z3::expr> &p) { return p.first == p.second; })
                               | util.reduce_and();

        res = utils::substitute_all(res, replacements) && constraints;
        write_log("exp substitutions:\n" << res);
    }

#if !EXTENDED_COMPS
    res = utils::replace_eq(res);
    write_log("replace equalities:\n" << res);
#endif
    return { simple, res.simplify(), common_base };
}

}
