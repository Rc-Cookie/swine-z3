#pragma once

#include "util.h"
#include "comparison.h"

#include <z3++.h>
#include <map>

namespace swine {

    /**
     * Represents a comparison from the extended "PowerComp" fragment, that is, a comparison of one of the forms of
     * <ul>
     *   <li>a * exp(x) < b</li>
     *   <li>a * exp(x) < b * exp(y)</li>
     *   <li>a * exp(x) <= b</li>
     *   <li>a * exp(x) <= b * exp(y)</li>
     *   <li>a * exp(x) = b</li>
     *   <li>a * exp(x) = b * exp(y)</li>
     *   <li>a * exp(x) != b</li>
     *   <li>a * exp(x) != b * exp(y)</li>
     * </ul>
     * where x,y are variables and a,b are non-zero constants, and exp() is the exponential function for some arbitrary,
     * but fixed basis.
     */
    struct PowerComp {

        /**
         * Different kinds of relations between the left and right hand side of the comparison.
         */
        enum class Kind {
            /** a * exp(x) should be equal to b [* exp(y)]. */
            Equal,
            /** a * exp(x) should be different from b [* exp(y)]. */
            NotEqual,
            /**
             * a * exp(x) should be strictly less than b * [* exp(y)]. Only power comparisons of this
             * kind lay in the regular (non-extended) PowerComp fragment.
             */
            Less,
            /** a * exp(x) should be less or equal to b [* exp(y)]. */
            LessOrEqual
        };

        /** The base of the exponential function(s). */
        cpp_int base;
        /** The left hand side exp's coefficient. */
        cpp_int a;
        /** The left hand side exp's coefficient, or the right hand side constant (if there is no y). */
        cpp_int b;
        /** The exponent in the left hand side's exp. */
        z3::expr x;
        /** The exponent in the right hand side's exp, or an empty optional, if the right hand side has no exp. */
        std::optional<z3::expr> y;
        /** The relation of the left and right hand side. */
        Kind kind;

        /**
         * Creates a new comparison of the form a * exp(x) [<,<=,=,!=] b.
         */
        PowerComp(const cpp_int &base, const cpp_int &a, const z3::expr &x, const cpp_int &b, Kind kind);

        /**
         * Creates a new comparison of the form a * exp(x) [<,<=,=,!=] b * exp(y).
         */
        PowerComp(const cpp_int &base, const cpp_int &a, const z3::expr &x, const cpp_int &b, const z3::expr &y, Kind kind);

        /**
         * @return The left hand side's coefficient as a Z3 expression.
         */
        z3::expr a_expr() const;

        /**
         * @return The right hand side's coefficient / constant as a Z3 expression.
         */
        z3::expr b_expr() const;

        /**
         * Converts this power comparison back to a Z3 expression.
         *
         * @param util Instance of Util to construct exp() expressions
         * @return An equivalent Z3 expression
         */
        z3::expr as_expr(const Util &util) const;

        /**
         * Converts this power comparison back to a Comparison object.
         *
         * @param util Instance of Util to construct exp() expressions
         * @return An equivalent comparison
         */
        Comparison as_comparison(const Util &util) const;

        /**
         * Determines whether this comparison has a constant value, i.e. a call to linearize() would
         * result in true or false.
         *
         * @return Whether this power comparison has a constant value independent of the value(s) of x (and y).
         */
        bool is_const() const;

        /**
         * Returns an equivalent exp-free expression.
         *
         * @return An equivalent expression from the LIA fragment
         */
        z3::expr linearize() const;

        /**
         * Converts this power comparison to a string (in infix notation, not in smt2 format).
         *
         * @return A string representation of this power comparison
         */
        std::string to_string() const;

        /**
         * Attempts to parse the given expression into a power comparison. This is equivalent to
         * first parsing it into a comparison and then into a power comparison.
         *
         * @param comparison The expression to attempt to parse
         * @return An equivalent power comparison, or an empty optional, if the expression is not
         *         equivalent to a power comparison
         */
        static std::optional<PowerComp> try_parse(const z3::expr &comparison);

        /**
         * Attempts to parse the given comparison into a power comparison.
         *
         * @param comparison The comparison to attempt to parse
         * @return An equivalent power comparison, or an empty optional, if the comparison does not
         *         lay in the extended PowerComp fragment
         */
        static std::optional<PowerComp> try_parse(const Comparison &comparison);

    private:

        /**
         * Tries to determine from the signs of the coefficients a and b whether this comparison
         * can be evaluated without knowing the variable values.
         *
         * @return If true, then this power comparison is definitely constant. The opposite is not
         *         necessarily the case.
         */
        bool is_clearly_const() const;

        /**
         * Linearizes this power comparison, assuming kind == Kind::Less.
         */
        z3::expr linearize_less() const;

        /**
         * Linearizes this power comparison, assuming kind == Kind::Equal.
         */
        z3::expr linearize_equal() const;
    };

    std::ostream& operator<<(std::ostream &s, const PowerComp::Kind &kind);

    std::ostream& operator<<(std::ostream &s, const PowerComp &comp);

    /**
     * Returns an equivalent expression, where all variables from the specified list of variables,
     * that also only occur in comparisons or divisibility constraints from the extended PowerComp
     * fragment, are linearized, i.e. any exp(x) calls for such a variable x will be removed.
     *
     * @param expr The expression to linearize
     * @param variables The variables to consider for linearization
     * @return An equivalent expression, possibly completely or partially in LIA
     */
    z3::expr linearize(const z3::expr& expr, const std::vector<z3::expr> &variables);
}
