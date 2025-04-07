#include "preprocessor.h"

namespace swine {

Preprocessor::Preprocessor(Util &util): util(util), rewriter(util), constant_propagator(util) {}

z3::expr Preprocessor::preprocess(const z3::expr &term, bool advanced) {
    const auto log = [&](const z3::expr &term, const PreprocKind kind, const std::function<z3::expr(const z3::expr&)> &f){
        bool done {false};
        const z3::expr res {f(term)};
        if ((util.config.log || util.config.debug) && res.id() != term.id()) {
            if (!done) {
                std::cout << "preprocessing" << std::endl;
                std::cout << "original term:" << std::endl;
                std::cout << term << std::endl;
                done = true;
            }
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
    auto last {term};
    if (advanced && util.config.is_active(PreprocKind::Inlining) && util.config.is_active(LemmaKind::EIA_n)) {
        last = log(term.simplify(), PreprocKind::Inlining, utils::inline_constants);
    }
    auto cterm {do_cp(term)};
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
    }
    return res.simplify();
}

}
