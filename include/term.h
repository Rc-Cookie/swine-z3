#pragma once

#include <z3++.h>
#include <boost/multiprecision/cpp_int.hpp>
#include "util.h"

namespace swine {

    using namespace boost::multiprecision;

    /**
     * Represents a sum-term of the form "SUM(c_i * x_i) + c", where the c_i and c are
     * constants (with c_i non-zero), and the x_i are variable expressions. This is not
     * restricted to regular variables, it may also be exp(x,y) or x*y etc., with all
     * linear coefficients extracted into the c_i value.
     */
    struct Term {

        /**
         * Only serves as context which cannot be implied if variables is empty. The actual
         * expression has no further meaning.
         */
        z3::expr ctx;
        /**
         * The x_i variables (not ordered).
         */
        expr_set variables;
        /**
         * The c_i coefficients, mapped by the id of the respective x_i expressions from variables.
         */
        std::unordered_map<unsigned int, cpp_int> coefficients;
        /**
         * The constant term c added to the variable sum.
         */
        cpp_int constant;

    private:
        /**
         * Creates a zero-valued term.
         *
         * @param ctx The context expression, no further meaning
         */
        Term(const z3::expr &ctx, bool) : ctx(ctx) {
        }
    public:
        /**
         * Converts the given expression to a term, throwing an exception on parsing failure.
         *
         * @param term The term to parse
         */
        Term(const z3::expr &term);

        /**
         * Returns a new term with value 0 (no variables, constant = 0).
         *
         * @return A new 0-valued term with the same context
         */
        Term zero() const;

        /**
         * Creates a term with value 0 (no variables, constant = 0).
         *
         * @param ctx An expression used sole for its context. The actual expression has no
         *            further meaning.
         * @return A new 0-valued term
         */
        static Term zero(const z3::expr &ctx);

        /**
         * Sets the term to the value 0, clearing all variables and setting the constant to 0.
         */
        void set_zero() {
            variables.clear();
            coefficients.clear();
            constant = 0;
        }

        /**
         * Whether this term is constant, i.e. it has no variables.
         *
         * @return Whether this term has a constant value.
         */
        bool is_const() const {
            return variables.empty();
        }

        /**
         * Whether this term is homogeneous, i.e. its constant is 0.
         *
         * @return Whether this term has no constant offset
         */
        bool is_homogeneous() const {
            return constant == 0;
        }

        /**
         * Whether this term has the value 0, i.e. it has no variables and its constant is 0.
         *
         * @return Whether this term has the value 0
         */
        bool is_zero() const {
            return is_const() && is_homogeneous();
        }

        /**
         * @return The constant offset of this term as an expression.
         */
        z3::expr constant_expr() const {
            return utils::term(constant, ctx);
        }

        /**
         * Converts this term to an expression, excluding the constant offset.
         *
         * @return The homogeneous part of this term as expression
         */
        z3::expr homogeneous() const;

        /**
         * @return A range view of pairs {c_i, x_i}, i.e. each coefficient mapped to the respective
         *         variable expression.
         */
        auto var_sum() const {
            return variables | std::views::transform([&](const std::pair<unsigned int, z3::expr> &p) -> std::pair<cpp_int, z3::expr> { return { coefficients.at(p.first), p.second }; });
        }

        /**
         * Returns all "real" variables in this term (i.e., uninterpreted symbols with arity 0),
         * including variables only contained transitively in other variable expressions.
         *
         * @return All variables in this term
         */
        expr_set const_vars() const {
            expr_set vars;
            for(const auto &[_,var] : variables)
                utils::collect_vars(var, vars);
            return vars;
        }

        /**
         * Converts this term back to a Z3 expression.
         *
         * @return This term as expression
         */
        z3::expr to_expr() const {
            if(is_const())
                return constant_expr();
            if(is_homogeneous())
                return homogeneous();
            return homogeneous() + constant_expr();
        }

        /**
         * Negates this expression in-place, meaning all coefficients and the constant get negated.
         */
        void negate();

        /**
         * Adds the term "coeff * var" to this term in-place.
         *
         * @param coeff The coefficient to add (might be 0 or not)
         * @param var The variable (must be a pure variable expression, no coefficient will be extracted)
         */
        void add(const cpp_int &coeff, const z3::expr &var);

        /**
         * Adds the given term to this term in-place.
         *
         * @param t The term to add
         */
        void add(const Term &t);

        /**
         * Subtracts the given term from this term in-place.
         *
         * @param t The term to subtract from this
         */
        void subtract(const Term &t);

        /**
         * Multiplies this term and the given term into the third term as output. The third term's
         * initial value will be discarded. This and the multiplied with term are not modified.
         *
         * @param t The term to multiply with this term
         * @param res The term to write the output into
         */
        void multiply(const Term &t, Term &res) const;

        /**
         * Returns a new term resulting from multiplying this term and the given term.
         *
         * @param t The term to multiply this term with
         * @return The multiplication result
         */
        Term times(const Term &t) const {
            Term res = zero();
            multiply(t, res);
            return res;
        }

        /**
         * Computes the 1-norm of the given term (the sum of the absolute values of the coefficients and the constant).
         *
         * @param t The term to compute the 1-norm of
         * @return The term's 1-norm (non-negative)
         */
        static const cpp_int one_norm(const Term &t) {
            return abs(t.constant) + (t.coefficients
                                    | std::views::values
                                    | std::views::transform([](const cpp_int &c) { return (cpp_int) abs(c); })
                                    | range_utils::sum<cpp_int>());
        }

        /**
         * Tests whether this term and the given term are identical, ignoring the constant offset from
         * each term.
         *
         * @param t The term to compare to this term
         * @return True iff "variables" and "coefficients" are identical on this and the given term
         */
        const bool homogeneous_equals(const Term &t) const {
            // Implicitly compares variable expression ids
            return coefficients == t.coefficients;
        }

    private:
        /**
         * Parses the given expression into this term.
         *
         * @param term The expression to parse
         * @return Whether the expression could be parsed
         */
        bool populate(const z3::expr &term);
    public:

        /**
         * Parses the given expression into a term, throwing an exception if not a valid term.
         *
         * @param expr The expression to parse
         * @return The parsed term
         */
        static Term parse(const z3::expr &expr) {
            Term term = zero(expr);
            if(term.populate(expr))
                return term;
            throw z3::exception("Invalid term");
        }

        /**
         * Attempts to parse the given expression into a term.
         *
         * @param expr The expression to parse
         * @return The parsed term, or an empty optional if not possible
         */
        static std::optional<Term> try_parse(const z3::expr &expr) {
            Term term = zero(expr);
            if(term.populate(expr))
                return term;
            return { };
        }

        /**
         * Converts this term back to an equivalent Z3 expression.
         *
         * @return This term as expression
         */
        inline operator z3::expr() const {
            return to_expr();
        }

        /**
         * Renders this term as a string (not according to smt2 format, but in infix
         * notation).
         *
         * @return This expression as string
         */
        std::string to_string() const;
    };

    std::ostream& operator<<(std::ostream &s, const Term &t);
}
