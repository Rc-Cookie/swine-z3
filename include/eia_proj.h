#pragma once

#include "util.h"
#include "power_comp.h"

namespace swine {

    /**
     * Result of a projection function; a single case of the the case distinction in the projection.
     */
    struct ProjResult {
        /** The premise made because of the given interpretation. */
        z3::expr premise;
        /** The conclusion that follows out of the premise. */
        z3::expr conclusion;
    };

    /**
     * An instantiation of the EIA_n projection function, for a fixed input formula, that can be evaluated
     * for different approximations.
     */
    class EIAProj {

        /** Util instance containing the common base, and with a reference to write statistics into. */
        Util &util;
        /** The input formula to be projected. */
        const z3::expr original_formula;

    public:

        /**
         * Instantiates the projection function for the given input formula.
         *
         * @param util Util instance containing the common base, and with a reference to write statistics into
         * @param formula The input formula to be projected
         */
        EIAProj(Util &util, const z3::expr &formula);

        /**
         * Projects the input function based on the given LIA approximation.
         *
         * @param approximation The LIA approximation to use for the projection - must be a model of the
         *                      formula (but exp() can be interpreted arbitrarily)
         * @return A pair [premise, projection] where premise combines the premises made because of the approximation,
         *         and projection is the result of the projection, either true for "sat" or false for "unsat"
         */
        std::pair<z3::expr, bool> evaluateCase(const z3::model &approximation);

    private:

        /**
         * Projection based version of SimplifyDiv; replaces non-simple divisibility constraints by simple ones.
         *
         * @param formula The formula in which to remove non-simple constraints
         * @param varsAndExps All variables and exp() terms that occur in formula
         * @param approximation The LIA-approximation to be used for projection
         * @return The projection result, where the conclusion has only simple divisibility constraints
         */
        ProjResult abSimplifyDiv(const z3::expr &formula, const expr_set &varsAndExps, const z3::model &approximation);

        /**
         * Performs regular model-based projection, on multiple variables at once.
         *
         * @param formula The formulas from which to eliminate variables
         * @param variables The variables to remove, may only occur linearly in the formula
         * @param model The model to use for projection
         * @return The projected formula
         */
        z3::expr liaProject(const z3::expr &formula, const std::vector<Z3_app> &variables, const z3::model &model);

        /**
         * Projection based version of SemCover; replaces all comparisons not in the extended PowerComp fragment
         * for at least one of the given variables with comparisons from PowerComp.
         *
         * @param formula The formula from which to eliminate problematic comparisons
         * @param variables The variables in the formula
         * @param approximation The LIA-approximation to be used for projection
         * @return The projection result, where the conclusion has no problematic comparisons for at least one variable
         */
        ProjResult abSemCover(const z3::expr &formula, const std::vector<z3::expr> &variables, const z3::model &approximation);
    };

}
