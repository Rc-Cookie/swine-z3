#include <ranges>
#include "eia_proj.h"
#include "divisibility.h"
#include "util.h"

#define log(msg) _log(util.config, msg)
#define debug(msg) _debug(util.config, msg)

namespace swine {

    using namespace std::views;
    using namespace range_utils;
    using namespace z3;
    using namespace utils;


    EIAProj::EIAProj(Util &util, const expr &formula) : util(util), original_formula(formula) {
    }


    std::pair<z3::expr, bool> EIAProj::evaluateCase(const model &approximation) {

        expr formula = original_formula;

//        Timer timer;

        for(int iterations = 1;; iterations++) {

            debug("-------- EIA_" << util.base << " iteration #" << iterations << " --------");
            debug("Remaining formula: " << formula);

            const expr_set remainingVarsAndExps = variables_in(formula, true, true);
            const std::vector<expr> remainingVars = remainingVarsAndExps | values | filter(is_var) | to_vec<expr>();
//            util.stats.timings.eia_n_remove_unused += timer.get_and_reset();

            if(remainingVars.size() == remainingVarsAndExps.size()) {
                log("Fully linearized " << iterations << " iteration" << (iterations == 1 ? "" : "s"));
                // All linear, and approximation is already a model for linear terms
                return { /* Not the actual promises, but irrelevant */ util.top(), true };
            }

            // ELSE IF some x in X only appears linearly in phi
            const std::unordered_set<unsigned int> nonLinear = remainingVarsAndExps
                    | values
                    | filter(is_exp)
                    | transform([](const expr &exp){ return exp.arg(1).id(); })
                    | to<std::unordered_set<unsigned int>>();
            if(remainingVars.size() != nonLinear.size()) {

                const std::vector<Z3_app> onlyLinearly = remainingVars
                        | filter([&](const expr &v){ return !nonLinear.contains(v.id()); })
                        | to_vec<Z3_app>();
                debug(onlyLinearly.size() << " variable" << (onlyLinearly.size() == 1 ? "" : "s") << " only occurs linearly -> eliminating with MBP");

                expr projected = liaProject(formula, onlyLinearly, approximation);
//                std::cout << "Projected: " << Util::to_string(projected) << "\nSimplifying divisibility constraints" << std::endl;
                auto [premise, simplified] = abSimplifyDiv(projected, remainingVarsAndExps, approximation);
                // TODO: Validate approximation?
//                std::cout << "Simplified divs: " << Util::to_string(simplified) << "\nPremises from SimplifyDiv: " << Util::to_string(premise) << std::endl;
                if(!approximation.eval(simplified, true).is_true()) {
                    log("Approximation not a model SimplifyDiv projection after " << iterations << " iteration" << (iterations == 1 ? "" : "s"));
//                    util.stats.timings.eia_n_remove_linear += timer.get_and_reset();
                    return { premise && simplified != projected, false };
                }
                formula = simplified;
//                util.stats.timings.eia_n_remove_linear += timer.get_and_reset();
                continue;
            }
//            util.stats.timings.eia_n_remove_linear += timer.get_and_reset();

            debug("All variables occur in exp -> applying SemCover");

            // ELSE
            const auto [premise, projected] = abSemCover(formula, remainingVars, approximation);
            debug("SemCover result: " << projected);
//            std::cout << "Projected: " << Util::to_string(projected) << "\nPremises from SemCover: " << Util::to_string(premise) << std::endl;

            if(!approximation.eval(projected, true).is_true()) {
                log("Approximation not a model of SemCover projection after " << iterations << " iteration" << (iterations == 1 ? "" : "s"));
//                util.stats.timings.eia_n_sem_cover += timer.get_and_reset();
                return { premise && projected != formula, false };
            }

            formula = linearize(projected, remainingVars);
//            std::cout << "Linearized: " << Util::to_string(formula) << std::endl;

            if(!approximation.eval(formula, true).is_true()) {
                log("Approximation not a model of linearized formula after " << iterations << " iteration" << (iterations == 1 ? "" : "s"));
//                util.stats.timings.eia_n_sem_cover += timer.get_and_reset();
                return { projected != formula, false };
            }
//            util.stats.timings.eia_n_sem_cover += timer.get_and_reset();
        }
    }


    ProjResult EIAProj::abSimplifyDiv(const expr &formula, const expr_set &varsAndExps, const model &approximation) {

        // G <- set of non-simple divisibilities in phi
        const std::vector<Divisibility> divisibilities = Divisibility::all_in(formula)
                | filter([](const Divisibility &d){ return !d.is_simple(); })
                | to_vec<Divisibility>();

        if(divisibilities.empty())
            return { util.top(), formula };

        // d <- least common multiple of all divisors
        const cpp_int leastCommonMultiple = divisibilities
                | transform(Divisibility::get_divisor)
                | reduce<cpp_int>([](const cpp_int &a, const cpp_int &b){ return lcm(a,b); }, 1);
        const expr lcmExpr = term(leastCommonMultiple, formula);

        // rem : T -> [d] := t |-> A(t) mod d
        const std::unordered_map<unsigned int, expr> remainders = varsAndExps
                | values
                | transform([&](const expr &t) -> std::pair<unsigned int, expr> { return { t.id(), term(value(t, approximation) % leastCommonMultiple, t) }; })
                | to<std::unordered_map<unsigned int, expr>>();

        // pi <- And_(t in T) (d | t - rem(t))
        const expr premise = varsAndExps
                | values
                | transform([&](const expr &t){ return (t - remainders.at(t.id())) % lcmExpr == 0; })
                | util.reduce_and();

        // [r(a) / a]
        const std::vector<std::pair<expr, expr>> replacements = varsAndExps
                | values
                | transform([&](const expr &t) -> std::pair<expr,expr> { return { t, remainders.at(t.id()) }; })
                | to_pairs<expr>();

        // phi[r(a) / a | a in G]
        expr simplified = formula;
        for(const Divisibility &d : divisibilities)
            simplified = substitute(simplified, d.original, substitute_all(d.original, replacements));

        return { premise, simplified };
    }


    expr EIAProj::liaProject(const z3::expr &formula, const std::vector<Z3_app> &variables, const model &model) {
        if(variables.empty())
            return formula;

//        Timer timer;
        expr res = to_expr(util.ctx, Z3_qe_model_project(util.ctx, model, (unsigned int) variables.size(), &variables.at(0), formula));
//        util.stats.timings.eia_n_mbp += timer;

        return replace_ite(res);
    }


    ProjResult EIAProj::abSemCover(const expr &formula, const std::vector<expr> &variables, const model &approximation) {

//        std::cout << "---- SemCover ----\nVariables:" << std::endl;
//        for(const auto v : variables)
//            std::cout << Util::to_string(v) << " = " << Util::value(approximation.eval(v, true)) << std::endl;

        // x <- min{ x | x in X, A(|x|) >= A(|y|) for all y in X }
        const expr variable = *(variables
                | max<expr>([&](const expr &a, const expr &b){ return cmp_in_interp(approximation, abs(a), abs(b)) < 0; }));

        const expr absVar = abs(variable);
        const cpp_int absVarVal = value(absVar, approximation);

        // Pi <- And_(y in X) |x| > |y|
        expr premises = variables
                | filter([&](const expr &v){ return v.id() != variable.id(); })
                | transform([&](const expr &v){ return absVar >= abs(v); })
                | util.reduce_and();

        const expr &varInPower = util.make_exp(variable);

        // I <- set of inequalities in phi outside PowerComp in which x appears as a power
        const std::vector<Comparison> problematicComps = find_values_in_bools<Comparison>(formula, Comparison::try_parse)
                | filter([&](const Comparison &c){ return c.term.variables.contains(varInPower.id()) && !c.is_in_power_comp(); })
                | to_vec<Comparison>();

        debug("Inequalities outside PowerComp with " << varInPower << " (#" << problematicComps.size() << "):");
        for(const Comparison &c : problematicComps)
            debug("  " << c);

        // H <- { h | (h(X) + c < 0) in I; h homogeneous }
        const std::vector<std::vector<Comparison>> sameHomogeneous = Comparison::group_by_homogeneous(problematicComps);

        expr projected = formula;

        for(const std::vector<Comparison> &similarComps : sameHomogeneous) {

            const Comparison &similarComp = similarComps.at(0);

//        std::cout << "-- Handling inequalities like " << similarComp << " --" << std::endl;

            // 2^g <- 2^7 * (lambda( ||h||_1 + max{ |c| : (h + c < 0) in Phi } ))^2
            // <=>
            // g <- 7 + 2 * log( ||h||_1 + max{ |c| : (h + c < 0) in Phi } )
            // <=>
            // g <- 7 + 2 * log( max{ ||h + c||_1 : (h + c < 0) in Phi } )
            const cpp_int gVal = 7 + 2 * util.floor_log(*(problematicComps | transform(Comparison::one_norm) | max<cpp_int>()));
            const expr g = util.term(gVal);
            debug("g = " << gVal);

            const auto [premise, conclusion] = ([&]() -> ProjResult {

                if(absVarVal <= gVal) {
//                    std::cout << Util::to_string(variable) << " is 'small'" << std::endl;
                    return {
                            // |x| = j
                            absVar == util.term(absVarVal),
                            // gamma[2^j / exp(x)]
                            substitute(projected, varInPower, util.term(util.abs_pow(absVarVal)))
                    };
                }

                // V <- variables in h except x
                std::vector<expr> otherVars = similarComp.term.const_vars()
                        | values
                        | filter([&](auto &v){ return v.id() != variable.id(); })
                        | to_vec<expr>();
                // Arbitrary, but consistent ordering
                std::sort(otherVars.begin(), otherVars.end(), [](auto &a, auto &b){ return a.to_string() < b.to_string(); });

                for(const expr &v : otherVars) {
                    const cpp_int otherAbsVarVal = abs(value(v, approximation));
                    if(absVarVal <= gVal + otherAbsVarVal) {
//                        std::cout << Util::to_string(variable) << " is 'small' relative to " << Util::to_string(v) << std::endl;
                        const cpp_int j = absVarVal - otherAbsVarVal;
                        return {
                                // |x| > g /\ |x| = j + |x|
                                absVar > g && absVar == util.term(j) + abs(v),
                                // gamma[2^j * exp(v) / exp(x)]
                                substitute(projected, varInPower, util.term(util.abs_pow(j)) * util.make_exp(v))
                        };
                    }
                }

//                std::cout << Util::to_string(variable) << " is 'large' compared to all other variables" << std::endl;

                // beta <- |x| > g /\ (And_(u in V) |x| > g + |u|)
                const expr bigCondition = absVar > g && (otherVars
                        | transform([&](const expr &v){ return absVar > g + abs(v); })
                        | util.reduce_and());

                // a <- coefficient as exp(x) in h
                const cpp_int expCoeff =  similarComp.term.coefficients.at(varInPower.id());

                return {
                        bigCondition,
                        substitute_all(projected, similarComps | transform([&](const Comparison &c) -> std::pair<expr,expr> {
                            switch(c.kind) {
                                case Comparison::Kind::Equal:    return { c.original, util.bot() }; // x >> ... -> c*x + ... = 0 is false
                                case Comparison::Kind::NotEqual: return { c.original, util.top() }; // x >> ... -> c*x + ... != 0 is true
                                case Comparison::Kind::Less:     return { c.original, util.bool_expr(expCoeff < 0) }; // x >> ... -> c*x + ... < 0 iff c < 0
                            }
                            throw std::runtime_error("Unknown comparison kind");
                        }))
                };
            })();

            premises = premises.is_true() ? premise : premises && premise;
            projected = conclusion.simplify();

            // IF gamma in { top, false }
            if(projected.is_true() || projected.is_false())
                break;
        }

//    std::cout << "---- End SemCover ----" << std::endl;
        return { premises, projected };
    }
}
