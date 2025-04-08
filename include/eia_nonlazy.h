#pragma once

#include <vector>
#include <deque>
#include <z3++.h>
#include "util.h"
#include "divisibility.h"

namespace swine {

    /**
     * Standalone solver for the EIA_n fragment (excluding preprocessing), implementing the "standard"
     * non-projection-based algorithm from "The Complexity of Presburger Arithmetic with Power or Powers"
     * by M. Benedikt et al., with support for the extended PowerComp fragment and optimized SemCover case
     * selection.
     */
    class EIANSolver {

        /** Util instance with config, common base and statistics to be written to. */
        Util &util;
        /** Solver used to eliminate infeasible cases in SemCover, and to check linear formulas. */
        z3::solver solver;
        /** Z3 tactic to perform quantifier elimination. */
        z3::tactic quantifierElimination;
        /**
         * List of formulas still to be processes for solving the current formula. The input formula is
         * always (between iterations) equivalent to the disjunction over these formulas. It corresponds
         * to the set "Q" from the pseudocode algorithm, where the variables are implied from the
         * variables remaining in each corresponding formula.
         */
        std::deque<z3::expr> todo;
        /**
         * Each exp() expression from the current formula, mapped to a fresh variable. Required for
         * Z3 quantifier elimination, since that doesn't seem to support uninterpreted functions, so
         * we temporarily have to replace exp() expressions with variables.
         */
        std::vector<std::pair<z3::expr, z3::expr>> expsToVars;
        /**
         * The inverse of "expsToVars" - maps the fresh variables back to the original exp() expressions.
         * This does not encode any new information that cannot be derived from expsToVars, but is used
         * as cache to avoid having to construct it newly for every quantifier elimination.
         */
        std::vector<std::pair<z3::expr, z3::expr>> varsToExps;

        /**
         * Implementation of the (fixed) PresQE algorithm for several variables at once. Eliminates the
         * specified variables from the formula, which may only occur linearly, only producing simple
         * divisibility constraints. Z3 built-in quantifier elimination is used to perform the regular
         * quantifier elimination, rather than a self-written copy of the PresQE "regular QE" part.
         * Because that does not support uninterpreted functions, we need to (temporarily) replace the
         * exp() expressions with fresh variables. For performance reasons, these are reused and thus
         * must be given calling the function. The resulting disjuncts will be written back into the
         * to-do list.
         *
         * @param formula The formula from which to eliminate the variables
         * @param vars The variables to eliminate from the formula, must only occur linearly
         * @param expsToVars A vector mapping all exp() expressions in the formula to fresh variables
         * @param varsToExps The inverse of "expsToVars", mapping the variables back to the exp() expressions
         */
        void presQE(const z3::expr &formula, const std::vector<z3::expr> &vars);

        /**
         * Recursive implementation of the loop over all mappings of remainders in SimplifyDiv. Replaces
         * the expressions from "fromIndex" in the keys of "currentRemainders" in the given divisibility
         * constraints with all possible remainders < lcm. The variables before "fromIndex" will always
         * be replaced by the values currently mapped to in the "currentRemainders" vector.
         *
         * @param formula The formula containing the divisibility
         * @param divisibilities All non-simple divisibilities in the formula
         * @param fromIndex The index from which to replace with all possible remainders, the other expressions
         *                  will only be replaced with their current value in "currentRemainders"
         * @param allRemainders The numbers from 0 to lcm-1 (inclusive), as Z3 expressions, to avoid having
         *                      to repeatedly instantiating Z3 expressions
         * @param lcm The least common multiple of all divisors from the divisibility constraints, as Z3
         *            expression
         * @param currentRemainders In the keys, all exp() and variable expressions occurring in the divisibility
         *                          constraints. In the values up to "fromIndex" the remainder to substitute for
         *                          that variable. The other remainders are ignored and will be overwritten
         */
        void addAllRemainders(const z3::expr &formula, const std::vector<Divisibility> &divisibilities, size_t fromIndex, const std::vector<z3::expr> &allRemainders, const z3::expr &lcm, std::vector<std::pair<z3::expr,z3::expr>> &currentRemainders);

        /**
         * Implementation of the SimplifyDiv algorithm. Eliminates any non-simple divisibility constraints
         * and replaces them by a disjunction of simple ones. Writes the resulting disjuncts separately into
         * the to-do list.
         *
         * @param formula The formula from which to eliminate the non-simple divisibility constraints
         * @param out List to append the resulting formulas to, adding each disjunct separately
         */
        void simplifyDiv(const z3::expr &formula);

        /**
         * Tests whether the current solver state is feasible, meaning that Z3 finds it satisfiable (but may
         * interpret exp() arbitrarily).
         *
         * @param kind The kind of formula in context. If infeasible, a message "{kind} infeasible" will be logged
         * @return Whether the current solver state is feasible
         */
        bool feasible(const std::string &kind);

        /**
         * Tests whether the given formula is feasible in the current solver state, meaning that Z3 finds it
         * satisfiable (but may interpret exp() arbitrarily). The solver's state will not be modified.
         *
         * @param formula The formula to check for feasibility, together with all the formulas already added
         *                to the solver
         * @param kind The kind of formula in context. If infeasible, a message "{kind} infeasible" will be logged
         * @return Whether the formula is feasible in the current solver context
         */
        bool feasible(const z3::expr &formula, const std::string &kind);

        /**
         * If feasibility checking for intermediate SemCover results is enabled, the expression is only added
         * to the buffer if it is feasible in the current solver context (see feasible(expr, string)). Otherwise
         * the expression is always added to the buffer, and no further logic happens.
         *
         * @param buffer The vector (possibly) append the expression to
         * @param e The expression to (possibly) add to the buffer
         */
        void maybeEmplace(std::vector<z3::expr> *buffer, const z3::expr &e);

        /**
         * Implementation of Linearize(SemCover(...)). Produces an equivalent disjunction, where, in each disjunct,
         * at least one of the variables only occurs linearly. Supports the extended PowerComp fragment, and
         * optimizes by skipping branches which are found trivially infeasible. Writes the resulting disjuncts
         * separately into the to-do list.
         *
         * @param formula The formula from which to linearize some variables
         * @param vars The variables to linearize
         */
        void semCoverAndLinearize(const z3::expr &formula, const std::vector<z3::expr> &vars);

    public:

        /**
         * Creates a new EIA_n solver. Even though the input formula is not specified, it is not thread-safe.
         *
         * @param util Util instance with configuration, common base and statistics to write to
         */
        EIANSolver(Util &util);

        /**
         * Checks whether the given formula in the reduced EIA_n fragment is satisfiable.
         *
         * @param formula The formula to test
         * @return sat or unsat, depending on the satisfiability of the formula
         */
        z3::check_result check(const z3::expr &formula);
    };
}
