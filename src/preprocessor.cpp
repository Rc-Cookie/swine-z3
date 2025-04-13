#include "preprocessor.h"
#include "config.h"

#define write_log(msg) _log(util.config, msg)
#define write_debug(msg) _debug(util.config, msg)

namespace swine {

using namespace range_utils;
using namespace std::views;

Preprocessor::Preprocessor(Util &util): util(util), rewriter(util), constant_propagator(util) {}

z3::expr Preprocessor::preprocess(const z3::expr &term, bool advanced) {
    const auto log = [&](const z3::expr &term, const PreprocKind kind, const std::function<z3::expr(const z3::expr&)> &f){
        bool done {false};
        const z3::expr res {f(term)};
        if ((util.config.log || util.config.debug) && res.id() != term.id()) {
//            if (!done) {
//                std::cout << "preprocessing" << std::endl;
//                std::cout << "original term:" << std::endl;
//                std::cout << term << std::endl;
//                done = true;
//            }
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
    if (advanced && util.config.is_active(PreprocKind::Inlining) && util.config.is_active(LemmaKind::EIA_n)) {
        last = log(term.simplify(), PreprocKind::Inlining, utils::inline_constants);
    }
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
    if (advanced && util.config.is_active(LemmaKind::EIA_n)) {
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
    }
    return res.simplify();
}

}
