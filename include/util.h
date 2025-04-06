#pragma once

#include <z3++.h>
#include <boost/multiprecision/cpp_int.hpp>

#include "config.h"
#include "stats.h"

namespace swine {

using namespace boost::multiprecision;

/**
 * Utility functions for Z3 related stuff that don't require additional context.
 */
namespace utils {

    /**
     * Converts the given number expression into a boost::multiprecision::cpp_int.
     *
     * @param term The numeric term, must be an integer numeral
     * @return The value as a cpp_int
     */
    cpp_int value(const z3::expr &term);

    /**
     * Evaluates the given expression in the specified interpretation and converts
     * the result into a boost::multiprecision::cpp_int.
     *
     * @param term The term, must be of sort int and resolve to a numeral when evaluating
     * @param interpretation The interpretation in which to evaluate the expression
     * @return The value in the interpretation as cpp_int
     */
    cpp_int value(const z3::expr &term, const z3::model &interpretation);

    /**
     * Converts the given number to a long long, throwing an swine::ExponentOverflow
     * exception if out of range.
     *
     * @param term The numeric term, must be an integer numeral
     * @return The value as a long long
     */
    long long to_int(const z3::expr &term);

    /**
     * Determines whether the given expression is a constant with a concrete value, e.g.
     * a number of one of "true" and "false" (as opposed to variables, functions etc.).
     *
     * @param expr The expression in question
     * @return True iff the expression has a ground value
     */
    bool is_value(const z3::expr &expr);

    /**
     * Returns whether the given expression is a kind of uninterpreted expression.
     *
     * @param expr The expression in question
     * @param vars Whether to look for variables (arity = 0)
     * @param functions Whether to look for functions (arity > 0)
     * @return Whether the expression is an uninterpreted expression of the given kind
     */
    bool is_uninterpreted(const z3::expr &expr, bool vars, bool functions);

    /**
     * Returns whether the given expression is a variable.
     *
     * @param expr The expression in question
     * @return Whether the expression is a (0-arity) variable
     */
    bool is_var(const z3::expr &expr);

    /**
     * Returns whether the given expression is a variable or function.
     *
     * @param expr The expression in question
     * @return Whether the expression is an (uninterpreted) function with 0 or more arguments
     */
    bool is_var_or_func(const z3::expr &expr);

    /**
     * Returns whether the given expression is an (uninterpreted) function.
     *
     * @param expr The expression in question
     * @return Whether the expression is a function (with arity > 0)
     */
    bool is_func(const z3::expr &expr);

    /**
     * Determines whether the given expression is an invocation of the exp() function.
     *
     * @param expr The expression in question
     * @return True iff the expression is "exp(*,*)"
     */
    bool is_exp(const z3::expr &expr);

    /**
     * Converts the given number to a Z3 expression, extracting the context from
     * the expression in the second argument.
     *
     * @param value The numeric value for the expression
     * @param ctx Anx z3::expr, only z3::expr::ctx() is relevant
     * @return A z3::expr with the same numeric value of sort int
     */
    z3::expr term(const cpp_int &value, const z3::expr &ctx);
}



class ExponentOverflow: public std::out_of_range {

    z3::expr t;

public:

    ExponentOverflow(const z3::expr &t);

    z3::expr get_t() const;

};

/**
 * Contains utilities that require additional SwInE context.
 */
class Util {

public:

    const Config &config;
    Statistics &stats;
    z3::context &ctx;
    std::unique_ptr<z3::func_decl> exp;

    Util(z3::context &ctx, const Config &config, Statistics &stats);

    /**
     * Converts the given number to a Z3 expression.
     *
     * @param value The numeric value for the expression
     * @return A z3::expr with the same numeric value of sort int
     */
    z3::expr term(const cpp_int &value);

    /**
     * Creates the expression exp(base, exponent).
     *
     * @param base The first argument for the exp call
     * @param exponent The second argument for the exp call
     * @return The exp expression
     */
    z3::expr make_exp(const z3::expr &base, const z3::expr &exponent);
};



}
