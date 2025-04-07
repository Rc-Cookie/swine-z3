#pragma once
#include "term.h"

namespace swine {

    /**
     * Represents a divisibility constraint of the form (d | t) ("d divides t"), where t is
     * a numeric term and d is a positive integer. These constraints are represented as
     * "(= (mod t d) 0)" or "t % d = 0" in Z3 (as there is no native constraints for
     * divisibility constraints).
     */
    struct Divisibility {

        /**
         * The term to be divisible by some constant.
         */
        Term dividend;
        /**
         * The divisor that should be a factor of the dividend. When parsed from an expression,
         * this value will be normalized to a value in the range [0, dividend.constant).
         */
        cpp_int divisor;
        /**
         * If this divisibility was parsed from an expression, then this is the original expression.
         * Otherwise, this has an arbitrary value.
         */
        z3::expr original;

        /**
         * Converts the given Z3 expression to a divisibility constraint, throwing an exception if
         * the given expression does not represent a valid divisibility constraint.
         *
         * @param divisibility The expression to parse
         */
        Divisibility(const z3::expr &divisibility);

        /**
         * Creates a new divisibility constraint.
         *
         * @param dividend The term to be divided
         * @param divisor The term to be a factor of the dividend
         * @param original The valid for the "original" field
         */
        Divisibility(const Term &dividend, const cpp_int &divisor, const z3::expr &original);

        /**
         * @return The divisor of this divisibility constraint as a Z3 expression.
         */
        z3::expr divisor_expr() const;

        /**
         * Converts this divisibility constraint back to a Z3 expression of the form "t % d = 0".
         *
         * @return An equivalent Z3 expression
         */
        z3::expr to_expr() const;

        /**
         * Determines whether this divisibility constraint has a constant value (true or false),
         * independent of the values of the variables of the dividend.
         *
         * @return Whether linearize() would return one of true or false
         */
        bool is_const() const;

    private:

        /**
         * Determines whether this constraint is "simple", that is, it is constant or has only one
         * variable expression in the term, which matches the given requirement.
         *
         * @param var_requirement The requirement for a variable, if there is one
         * @return Whether this constraint is simple with the given requirement
         */
        bool is_simple(const std::function<bool(const z3::expr &)> &var_requirement) const;

    public:

        /**
         * Determines whether this constraint is in the PowerComp fragment, that is, it is constant
         * or of the form (d | exp(x) - r), where x is a variable and r a positive integer.
         *
         * @return Whether this constraint is in the PowerComp fragment
         */
        bool is_in_power_comp() const;

        /**
         * Determines whether this constraint is "simple", that is, it is constant or of the form
         * (d | x - r) or (d | exp(x) - r), where x is a variable and r a positive integer.
         *
         * @return Whether this constraint is "simple"
         */
        bool is_simple() const;

        /**
         * Returns an equivalent Z3 expression (possibly representing a divisibility constraint again,
         * but not necessarily) in LIA. This constraint must be in the PowerComp fragment according to
         * is_in_power_comp().
         *
         * @return An equivalent LIA expression
         */
        z3::expr linearize() const;

        /**
         * @return c.dividend
         */
        static const Term &get_dividend(const Divisibility &c);

        /**
         * @return c.divisor
         */
        static const cpp_int &get_divisor(const Divisibility &c);

        /**
         * Attempts to parse the given term into a divisibility constraint.
         *
         * @param divisibility The expression to parse
         * @return The parsed divisibility constraint, or an empty optional, if the given expression
         *         does not represent a valid divisibility constraint
         */
        static std::optional<Divisibility> try_parse(const z3::expr &divisibility);

        /**
         * Parses the given term into a divisibility constraint, throwing an exception if it does not
         * represent a valid divisibility constraint.
         *
         * @param divisibility The expression to parse
         * @return The parsed divisibility constraint
         */
        static Divisibility parse(const z3::expr &divisibility);

        /**
         * Returns all divisibility constraints in the given formula.
         *
         * @param formula The formula from which to extract all divisibility constraints
         * @return All divisibility constraints from the formula, in no particular order, possibly with
         *         duplicates
         */
        static std::vector<Divisibility> all_in(const z3::expr &formula);

        /**
         * Converts this divisibility constraint into a string (infix notation, not in smt2 format!).
         *
         * @return A string representation of this constraint
         */
        std::string to_string() const;
    };

    std::ostream& operator<<(std::ostream &s, const Divisibility &d);
}
