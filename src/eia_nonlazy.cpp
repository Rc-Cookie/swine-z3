#include "eia_nonlazy.h"
#include "divisibility.h"
#include "power_comp.h"

// Order in which to process the to-do list
#define BREATH_FIRST 0

// Whether to preemptively perform case distinctions instead of using ITEs for abs()
#define SPLIT_ABS 1
// Whether to check LIA-satisfiability of each set of cases with the same largest
// variable (and the same variable signs, of SPLIT_ABS is enabled)
#define CHECK_SEM_COVER_BRANCH_FEASIBILITY 1
// Whether to check LIA-satisfiability of each intermediate generated case in SemCover
#define CHECK_SEM_COVER_INTERMEDIATE_FEASIBILITY 1

#define CHECK_SEM_COVER_FEASIBILITY (CHECK_SEM_COVER_INTERMEDIATE_FEASIBILITY || (SPLIT_ABS && CHECK_SEM_COVER_BRANCH_FEASIBILITY))

#define log(msg) _log(util.config, msg)
#define debug(msg) _debug(util.config, msg)

namespace swine {

    using namespace z3;
    using namespace std::views;
    using namespace range_utils;
    using namespace utils;


    EIANSolver::EIANSolver(swine::Util &util) : util(util), solver(util.ctx), quantifierElimination(util.ctx, "qe") {
    }


    z3::check_result EIANSolver::check(const expr &original_formula) {

        debug("Checking " << original_formula);

        solver.reset();
        todo.clear();
        // Add to to-do list, simplifying and non-simple divisibilities
        simplifyDiv(original_formula);

        const expr_set exps = find(original_formula, is_exp) | to<expr_set>();
        expsToVars = exps | values
                | transform([&](const expr &exp) -> std::pair<expr,expr> { return { exp, util.new_variable() }; })
                | to_pairs<expr>();
        varsToExps = expsToVars
                | transform([&](const std::pair<expr,expr> &p) -> std::pair<expr,expr> { return { p.second, p.first }; })
                | to_pairs<expr>();

        size_t iterations = 0, branches = 0;

        while(!todo.empty()) {
            util.stats.iterations++;
            iterations++;
            debug("------------ Iteration #" << iterations << " - #todo: " << todo.size() << " ------------");

            // (X,phi) <- pop(Q)
#if BREATH_FIRST
            const expr formula = todo.front();
            todo.pop_front();
#else
            const expr formula = todo.back();
            todo.pop_back();
#endif
            debug("Processing: " << formula);

            const expr_set remainingVarsAndExps = variables_in(formula, true, true);

            // IF X empty
            if(remainingVarsAndExps.empty()) {
                branches++;
                if(formula.simplify().is_true()) {
                    log("sat in " << branches << " branch" << (branches == 1 ? "" : "es") << " and " << iterations << " iterations with " << todo.size() << " formula" << (todo.size() == 1 ? "" : "s") << " still queued");
                    return sat;
                }
                assert(formula.simplify().is_false());
                debug("Branch is unsatisfiable");
                continue;
            }

            const std::vector<expr> remainingVars = remainingVarsAndExps | values | filter(is_var) | to_vec<expr>();

            if(remainingVars.size() == remainingVarsAndExps.size()) {
                // No exp() -> fully linearized -> solve directly with Z3 (most likely faster than solving via QE)
                branches++;
                if(!feasible(formula, "Branch", util.stats.timings.eia_iter_qe))
                    continue;
                log("sat of linear formula in " << branches << " branch" << (branches == 1 ? "" : "es") << " and " << iterations << " iterations with " << todo.size() << " formula" << (todo.size() == 1 ? "" : "s") << " still queued");
                return sat;
            }

            // IF some x in X only occurs linearly in phi
            const std::unordered_set<unsigned int> nonLinear = remainingVarsAndExps
                    | values
                    | filter(is_exp)
                    | transform([](const expr &exp){ return exp.arg(1).id(); })
                    | to<std::unordered_set<unsigned int>>();
            if(remainingVars.size() != nonLinear.size()) {

                const std::vector<expr> onlyLinearly = remainingVars
                        | filter([&](const expr &v){ return !nonLinear.contains(v.id()); })
                        | to_vec<expr>();

                debug("Eliminating only linear occurring variables " << onlyLinearly << " with QE");
                // Q <- Q union FixedPresQE(x,X,Phi)
                presQE(formula, onlyLinearly);
            }
            else {
                log("Applying SemCover to " << remainingVars.size() << " variable" << (remainingVars.size() == 1 ? "" : "s") << " ...");
                size_t oldCount = todo.size();
                // Q <- Q union Linearize(SimpleSemCover(phi))
                semCoverAndLinearize(formula, remainingVars);
                log("Generated " << (todo.size() - oldCount) << " case" << (todo.size() - oldCount == 1 ? "" : "s") << " in SemCover");
            }
        }
        log("unsat after " << branches << " branch" << (branches == 1 ? "" : "es") << " and " << iterations << " iterations");
        return unsat;
    }


    void EIANSolver::presQE(const expr &formula, const std::vector<expr> &vars) {

        Timer timer;

        // Convert to Z3 vector
        expr_vector vars_vec = { util.ctx };
        for(const z3::expr &v : vars)
            vars_vec.push_back(v);

        // Replace exp() expressions with fresh variables, because the Z3 QE does not seem to work
        // with uninterpreted functions
        expr withoutExp = substitute_all(formula, expsToVars);
        debug("Without exps():\n" << withoutExp);

        expr quantified = exists(vars_vec, withoutExp);
        goal goal = { util.ctx };
        goal.add(quantified);

        apply_result qeRes = quantifierElimination.apply(goal);
        debug("Z3 QE result:\n" << qeRes);

        for(unsigned int i=0; i<qeRes.size(); i++) {
            // Undo exp() substitutions
            expr qfFree = substitute_all(qeRes[i].as_expr(), varsToExps);
            debug("With variables:\n" << qeRes[i].as_expr());
            debug("With exps():\n" << qfFree);
            util.stats.timings.eia_iter_qe += timer;
            simplifyDiv(qfFree);
            timer.reset();
        }
    }


    void EIANSolver::addAllRemainders(const expr &formula, const std::vector<Divisibility> &divisibilities, size_t fromIndex, const std::vector<expr> &allRemainders, const expr &lcm, std::vector<std::pair<expr,expr>> &currentRemainders) {
        if(fromIndex < currentRemainders.size()) {
            // Pointer to the current expression's remainder
            expr &curRemainder = currentRemainders.at(fromIndex).second;
            fromIndex++;
            // Iterate over all possible remainders of the expression at fromIndex
            for(const expr &r : allRemainders) {
                // Use this remainder for the current expression
                curRemainder = r;
                // Do the same for all subsequent expressions
                addAllRemainders(formula, divisibilities, fromIndex, allRemainders, lcm, currentRemainders);
            }
            return;
        }

        // Perform the substitution for a single mapping of remainders (the current one in currentRemainders)

        // phi[r(a) / a | a in G]
        expr branch = formula;
        for(const Divisibility &d : divisibilities) {
            // Replace expressions with remainders only in divisibilities - they are only their remainder not generally
            // valid in the rest of the formula
            branch = substitute(branch, d.original, substitute_all(d.original, currentRemainders));
        }

        // And(t in T) (d | t - r(t))
        for(const auto &[t,r] : currentRemainders)
            branch = branch && (t - r) % lcm == 0;

        todo.emplace_back(branch);
    }


    void EIANSolver::simplifyDiv(const expr &formula) {

        // Split ORs which would usually be done by PresQE
        if(formula.is_or()) {
            for(unsigned int i=0; i<formula.num_args(); i++)
                simplifyDiv(formula.arg(i));
            return;
        }

        Timer timer;

        // G <- set of non-simple divisibilities in phi
        const std::vector<Divisibility> divisibilities = Divisibility::all_in(formula)
                | filter([](const Divisibility &d){ return !d.is_simple(); })
                | to_vec<Divisibility>();

        if(divisibilities.empty()) {
            util.stats.timings.eia_iter_simplify_div += timer;
            todo.emplace_back(formula);
            return;
        }

        // d <- least common multiple of all divisors
        const cpp_int leastCommonMultiple = divisibilities
                | transform(Divisibility::get_divisor)
                | reduce<cpp_int>([](const cpp_int &a, const cpp_int &b){ return lcm(a,b); }, 1);
        const expr lcmExpr = util.term(leastCommonMultiple);

        // T <- all variables x and powers exp(y) appearing in G
        const auto varsAndExps = variables_in(formula, true, true);

        std::vector<std::pair<expr, expr>> remainderBuffer = varsAndExps
                | values
                | transform([](const expr &v) -> std::pair<expr,expr> { return { v, /* The second value is irrelevant, as it will be overridden anyway */ v }; })
                | to_pairs<expr>();

        std::vector<expr> precomputedRemainders;
        for(cpp_int r=0; r<leastCommonMultiple; ++r)
            precomputedRemainders.emplace_back(util.term(r));

        addAllRemainders(formula, divisibilities, 0, precomputedRemainders, lcmExpr, remainderBuffer);

        util.stats.timings.eia_iter_simplify_div += timer;
    }

    bool EIANSolver::feasible(const std::string &kind, Timer::duration &stat) {
        Timer timer;
        check_result res = solver.check();
        stat += timer;
        if(res == sat)
            return true;
        if(res == unknown)
            throw z3::exception("Z3 returned unknown");
        log(kind << " infeasible");
        return false;
    }

    bool EIANSolver::feasible(const z3::expr &formula, const std::string &kind, Timer::duration &stat) {
        Timer timer;
        solver.push();
        solver.add(formula);
        stat += timer;
        bool res = feasible(kind, stat);
        timer.reset();
        solver.pop();
        stat += timer;
        return res;
    }

    void EIANSolver::maybeEmplace(std::vector<expr> *buffer, const expr &e) {
#if CHECK_SEM_COVER_INTERMEDIATE_FEASIBILITY
        if(feasible(e, "SemCover intermediate case", util.stats.timings.eia_iter_feasibility))
            buffer->emplace_back(e);
#else
        buffer->emplace_back(e);
#endif
    }

    void EIANSolver::semCoverAndLinearize(const expr &formula, const std::vector<expr> &vars) {

        Timer timer;

        std::vector<Comparison> allProblematicComps = find_values_in_bools<Comparison>(formula, Comparison::try_parse)
                | filter([](const Comparison &c){ return !c.is_in_power_comp(); })
                | to_vec<Comparison>();
        if(allProblematicComps.empty()) {
            log("No problematic comparisons -> linearizing directly");
            // No case selection, just linearize
            todo.emplace_back(linearize(formula, vars));
            return;
        }

#if CHECK_SEM_COVER_FEASIBILITY
        solver.push();
        solver.add(formula);
        if(!feasible("SemCover input formula", util.stats.timings.eia_iter_feasibility)) {
            util.stats.timings.eia_iter_sem_cover += timer;
            return;
        }
#endif

        std::unordered_map<unsigned int, size_t> varIndices;
        for(size_t i=0; i<vars.size(); i++)
            varIndices.emplace(vars.at(i).id(), i);

        // FOR x in X
        for(const expr &var : vars) {

            log("Generating SemCover cases where " << var << " is the largest variable");

            // Cache exp(x) expression
            const expr &varInPower = util.make_exp(var);

            // I <- set of inequalities in phi outside PowerComp in which x appears as a power
            const std::vector<Comparison> problematicComps = allProblematicComps
                    | filter([&](const Comparison &c){ return c.term.variables.contains(varInPower.id()); })
                    | to_vec<Comparison>();

            if(problematicComps.empty()) {
                log(var << " is not problematic -> linearizing directly");
                // No case selection, just linearize (with the precondition that x = max(X))
                const expr varIsLargestSimple = vars
                        | filter([&](const expr &v){ return v.id() != var.id(); })
                        | transform([&](const expr &v){ return abs(var) >= abs(v); })
                        | util.reduce_and();
                const expr varIsLargest = replace_ite(varIsLargestSimple);
                todo.emplace_back(varIsLargest && linearize(formula, vars));
                continue;
            }

            // H <- { h | (h(X) + c < 0) in I; h homogeneous }
            const std::vector<std::vector<Comparison>> sameHomogeneous = Comparison::group_by_homogeneous(problematicComps);

#if SPLIT_ABS
            // Before this is an issue, we will run out of memory (and time)...
            assert(vars.size() < 64);
            // Instead of using abs() everywhere and eliminating them generically with remove_ite() afterwards,
            // explicitly construct each combination (where each variable is either negative or positive). This
            // produces smaller disjuncts, and we don't have to remove the ITEs afterwards, but the main benefit
            // is that it allows to then check the satisfiability of these preconditions alone (the signs of the
            // variables), which is particularly effective in nested SemCover invocations, where specific signs
            // are already implied.
            //
            // "signs" is a bitmask, where bit i being set means variable i is negative, otherwise non-negative
            for(size_t signs = 0, stop = 1 << vars.size(); signs < stop; signs++) {

                // The value of abs(var) with the current sign
                const auto varAbs = [&varIndices, signs](const expr &v){ return ((signs >> varIndices.at(v.id())) & 1) ? -v : v; };

                // Expression that asserts that the signs of the variables match that of the current value of the
                // "signs" bitmask
                expr precondition = vars
                        | transform([&varIndices, signs](const expr &v){ return ((signs >> varIndices.at(v.id())) & 1) ? v < 0 : v >= 0; })
                        | util.reduce_and();
                log("SemCover precondition: " << precondition);
#else
                // Simply produces the term "abs(x)" (i.e. (ite (>= x 0) x (- x)))
                const auto varAbs = [](const expr &v){ return abs(v); };
#endif

                const expr absVar = varAbs(var);
                // And_(y in X)(|x| > |y|)
                const expr varIsLargest = vars
                        | filter([&](const expr &v){ return v.id() != var.id(); })
                        | transform([&](const expr &v){ return absVar >= varAbs(v); })
                        | util.reduce_and();

#if CHECK_SEM_COVER_FEASIBILITY
                solver.push();
                solver.add(varIsLargest);
#if SPLIT_ABS
                solver.add(precondition);
#endif
#if CHECK_SEM_COVER_BRANCH_FEASIBILITY
                // Check whether these preconditions (signs of variables and the current variable being the largest)
                // conflict with the current formula - then we can skip all the cases generated for these
                // preconditions.
                if(!feasible("SemCover branch", util.stats.timings.eia_iter_feasibility)) {
                    solver.pop();
                    continue;
                }
#endif
#endif

                // We need one buffer for the previous iteration's results, and one to write the current iterations
                // results into. To avoid unnecessary copying, we simply swap two pointer back and forth.
                std::vector<expr> buffer1, buffer2;
                std::vector<expr> *transformed = &buffer1;
                std::vector<expr> *buffer = &buffer2;

                // Gamma_x <- { phi }
                transformed->emplace_back(formula);
                // FOR x in X
                for(const std::vector<Comparison> &similarComps : sameHomogeneous) {

                    const Comparison &similarComp = similarComps.at(0);
                    debug("Processing " << var << " in inequalities like " << similarComp);
                    buffer->clear();

                    // 2^g <- 2^7 * (lambda( ||h||_1 + max{ |c| : (h + c < 0) in Phi } ))^2
                    // <=>
                    // g <- 7 + 2 * log( ||h||_1 + max{ |c| : (h + c < 0) in Phi } )
                    // <=>
                    // g <- 7 + 2 * log( max{ ||h + c||_1 : (h + c < 0) in Phi } )
                    const cpp_int gVal = 7 + 2 * util.floor_log(*(problematicComps | transform(Comparison::one_norm) | max<cpp_int>()));
                    const expr g = util.term(gVal);

                    // a <- coefficient as exp(x) in h
                    const cpp_int expCoeff =  similarComp.term.coefficients.at(varInPower.id());

                    // V <- variables in h except x
                    // { [abs(v), exp(v)] | v in V }
                    std::vector<std::pair<expr,expr>> otherVars = similarComp.term.const_vars()
                            | values
                            | filter([&](auto &v) { return v.id() != var.id(); })
                            | transform([&](const auto &v) -> std::pair<expr,expr> { return { varAbs(v), util.make_exp(v) }; })
                            | to_pairs<expr>();

                    log("g = " << gVal << " -> generating " << (transformed->size() * ((gVal + 1) * (otherVars.size() + 1) + 1)) << " cases");

                    // beta <- |x| > g /\ (And_(u in V) |x| > g + |u|)
                    const expr bigCondition = varAbs(var) > g && (otherVars
                            | keys
                            | transform([&](const expr &absV){ return absVar > g + absV; })
                            | util.reduce_and());
                    // In the original algorithm this is simply gamma[true / a] or gamma[false / a], depending on
                    // the coefficient. With the extended PowerComp fragment, we have to replace differently
                    // depending on the kind of comparison
                    const std::vector<std::pair<expr, expr>> bigReplacements = similarComps
                            | transform([&](const Comparison &c) -> std::pair<expr,expr> {
                                switch(c.kind) {
                                    case Comparison::Kind::Equal:    return { c.original, util.bot() }; // x >> ... -> c*x + ... = 0 is false
                                    case Comparison::Kind::NotEqual: return { c.original, util.top() }; // x >> ... -> c*x + ... != 0 is true
                                    case Comparison::Kind::Less:     return { c.original, util.bool_expr(expCoeff < 0) }; // x >> ... -> c*x + ... < 0 iff c < 0
                                }
                                throw std::runtime_error("Unknown comparison kind");
                            })
                            | to_pairs<expr>();

                    // { [j, exp(j)] | 0 <= j <= g }
                    std::vector<std::pair<expr, expr>> js;
                    for(cpp_int j=0; j<=gVal; ++j)
                        js.push_back({ util.term(j), util.term(util.abs_pow(j)) });

                    for(const expr &disjunct : *transformed) {
                        for(const auto &[j, expJ] : js) {
                            // |x| = j /\ gamma[2^j / exp(x)]
                            maybeEmplace(buffer, absVar == j && substitute(disjunct, varInPower, expJ));
                            for(const auto &[absV, expV] : otherVars) {
                                // |x| = j + |v| /\ gamma[2^j * exp(v) / exp(x)]
                                maybeEmplace(buffer, absVar == j + absV && substitute(disjunct, varInPower, expJ * expV));
                            }
                        }
                        maybeEmplace(buffer, bigCondition && substitute_all(disjunct, bigReplacements));
                    }

#if CHECK_SEM_COVER_INTERMEDIATE_FEASIBILITY
                    log("Actually generated " << buffer->size() << " feasible cases");
#endif

                    std::swap(transformed, buffer);
                }

                log("Linearizing " << transformed->size() << " cases");
                // Linearize right here, so we can avoid creating another temporary buffer
                for(const expr &e : *transformed) {
#if SPLIT_ABS
                    util.stats.timings.eia_iter_sem_cover += timer.get_and_reset();
                    log("Linearizing " << (precondition && varIsLargest && e));
                    todo.emplace_back(precondition && varIsLargest && linearize(e, vars));
                    util.stats.timings.eia_iter_linearize += timer.get_and_reset();
#else
                    // Replace ITEs from abs, then split disjuncts
                    for(const expr &disjunct : find_bools(replace_ite(varIsLargest && e), [](const expr &e){ return !e.is_or(); })) {
                        util.stats.timings.eia_iter_sem_cover += timer.get_and_reset();
                        todo.emplace_back(linearize(disjunct, vars));
                        util.stats.timings.eia_iter_linearize += timer.get_and_reset();
                    }
#endif
                }

#if CHECK_SEM_COVER_FEASIBILITY
                solver.pop();
#endif
#if SPLIT_ABS
            }
#endif
        }
#if CHECK_SEM_COVER_FEASIBILITY
        solver.pop();
#endif
        util.stats.timings.eia_iter_sem_cover += timer;
    }
}
