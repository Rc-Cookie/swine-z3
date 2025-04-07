#pragma once

#include <z3++.h>
#include <boost/multiprecision/cpp_int.hpp>

#include "config.h"
#include "stats.h"
#include "range_utils.h"

namespace swine {

using namespace boost::multiprecision;

/**
 * A set of expressions, implemented by mapping each expression by their id in an unordered_map.
 */
class expr_set: public std::unordered_map<unsigned int, z3::expr> {
public:
    /**
     * Inserts the given expression into the expression set, if not already contained.
     *
     * @param expr The expression to insert
     * @return True if the expression was newly added, false if it was already in the set
     */
    bool add(const z3::expr &expr);

    /**
     * Removes the given expression from the expression set, if it was contained.
     *
     * @param expr The expression to remove
     * @return Whether the expression was previously in the set
     */
    bool erase(const z3::expr &expr);

    /**
     * Removes the given expression with the given id from the expression set, if such an
     * expression was contained.
     *
     * @param expr The expression id to remove
     * @return Whether the was previously an expression with that id in the set
     */
    bool erase(unsigned int expr_id);

    /**
     * Returns whether the given expression is in this set.
     *
     * @param expr The expression in question
     * @return True iff the expression is contained in this set
     */
    bool contains(const z3::expr &expr);

    /**
     * Returns whether an expression with the given id is in this set.
     *
     * @param expr_id The expression id in question
     * @return True iff the this set contains an expression with the given id
     */
    bool contains(unsigned int expr_id);
};

std::ostream& operator<<(std::ostream &s, const expr_set &set);

std::ostream& operator<<(std::ostream &s, const std::vector<z3::expr> &vec);


/**
 * A logical AND or OR range reduction operation.
 *
 * @tparam conjunction Whether this is an AND reduction
 */
template <bool conjunction>
struct logic_reduction {
    z3::context &ctx;
};

// Implementation of logic_reduction
template <std::ranges::range R, bool conjunction>
requires std::convertible_to<std::ranges::range_value_t<R>, z3::expr>
std::ranges::range_value_t<R> operator|(R&& r, const logic_reduction<conjunction> &red) {

    z3::context &ctx = red.ctx;

    std::vector<Z3_ast> args;
    for(const z3::expr &arg : r) {
        assert(arg.is_bool());
        Z3_inc_ref(ctx, arg);
        args.push_back(arg);
    }

    if(args.empty())
        return ctx.bool_val(conjunction);
    if(args.size() == 1) {
        Z3_dec_ref(ctx, args.at(0));
        return {ctx, args.at(0)};
    }

    Z3_ast res = conjunction ?
                 Z3_mk_and(ctx, args.size(), &args.at(0)) :
                 Z3_mk_or(ctx, args.size(), &args.at(0));

    for(const Z3_ast &arg : args)
        Z3_dec_ref(ctx, arg);
    ctx.check_error();
    return { ctx, res };
}


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

    /**
     * Searches the first expression recursively for an occurrence of the first expression.
     *
     * @param might_contain The expression in which to search
     * @param might_be_contained The expression to search for
     * @return True iff the second expression is contained in the first expression. This is
     *         also true if the two expressions are identical.
     */
    bool contains(const z3::expr &might_contain, const z3::expr &might_be_contained);

    /**
     * Recursively traverses the given expression and adds all variables and/or functions
     * into the given output set.
     *
     * @param expr The expression from which to collect the variables from
     * @param into The set to insert the variables into
     * @param vars Whether to collect variables (arity 0), by default true
     * @param functions Whether to collect functions (arity > 0), by default false
     */
    void collect_vars(const z3::expr &expr, expr_set &into, bool vars = true, bool functions = false);

    /**
     * Recursively collects all variables and/or functions in the given expression.
     *
     * @param expr The expression from which to return all contained variables
     * @param vars Whether to search for variables (arity 0), by default true
     * @param functions Whether to search for functions (arity > 0), by default false
     * @return All variables and/or functions, as configured, contained in the given expression
     */
    expr_set variables_in(const z3::expr &expr, bool vars = true, bool functions = false);

    namespace detail {
        /**
         * Recursively traverses the given expression, conditionally collecting some of them mapped to a different
         * value in the "dst" vector.
         *
         * @tparam R The type of values being mapped to
         * @param expr The expression to traverse
         * @param predicate A function applied to each sub-expression. Any non-empty result will be added to the
         *                  "dst" vector.
         * @param recurse A predicate to determine whether to traverse the sub-tree of a given expression, given
         *                the current expression and the result from "predicate" for that expression.
         * @param dst The vector to collect non-empty mapped values in
         */
        template <typename R>
        void walk_expr(const z3::expr &expr, const std::function<std::optional<R>(const z3::expr &)> &predicate, const std::function<bool(const z3::expr &, const std::optional<R> &)> &recurse, std::vector<R> &dst) {
            std::optional<R> value = predicate(expr);
            if(value)
                dst.push_back(*value);

            if(expr.is_app() && recurse(expr, value)) {
                unsigned int args = expr.num_args();
                for(unsigned int i=0; i<args; i++)
                    walk_expr(expr.arg(i), predicate, recurse, dst);
            }
        }
    }

    /**
     * Recursively traverses the given expression, conditionally collecting some of them mapped to a different value.
     *
     * @tparam R The type of values being mapped to
     * @param expr The expression to traverse
     * @param predicate A function applied to each sub-expression. Any non-empty result will be included in the returned
     *                  vector.
     * @param recurse A predicate to determine whether to traverse the sub-tree of a given expression, given the current
     *                expression and the result from "predicate" for that expression.
     * @return All non-empty results from "predicate"
     */
    template <typename R>
    std::vector<R> find_values_where(const z3::expr &expr, const std::function<std::optional<R>(const z3::expr &)> &predicate, const std::function<bool(const z3::expr &, const std::optional<R> &)> &recurse) {
        std::vector<R> found;
        detail::walk_expr<R>(expr, predicate, recurse, found);
        return found;
    }

    /**
     * Recursively traverses the given expression, conditionally collecting some of them mapped to a different value.
     *
     * @tparam R The type of values being mapped to
     * @param expr The expression to traverse
     * @param predicate A function applied to each sub-expression. Any non-empty result will be included in the returned
     *                  vector.
     * @param search_in_success Whether to traverse the sub-tree if "predicate" returned a non-empty result for a given
     *                          expression (skipped by default).
     * @param search_in_failed Whether to traverse the sub-tree if "predicate" returned an empty optional for a given
     *                         expression (true by default).
     * @return All non-empty results from "predicate"
     */
    template <typename R>
    std::vector<R> find_values(const z3::expr &expr, const std::function<std::optional<R>(const z3::expr &)> predicate, bool search_in_success = false, bool search_in_failed = true) {
        return find_values_where<R>(expr, predicate, [&](auto _, std::optional<R> r){ return r ? search_in_success : search_in_failed; });
    }

    /**
     * Recursively traverses the given boolean-sorted parts of the expression, conditionally collecting some of them
     * mapped to a different value.
     *
     * @tparam R The type of values being mapped to
     * @param expr The expression to traverse
     * @param predicate A function applied to each sub-expression of sort bool. Any non-empty result will be included
     *                  in the returned vector.
     * @param search_in_success Whether to traverse the sub-tree if "predicate" returned a non-empty result for a given
     *                          expression (skipped by default).
     * @param search_in_failed Whether to traverse the sub-tree if "predicate" returned an empty optional for a given
     *                         expression (true by default).
     * @return All non-empty results from "predicate"
     */
    template <typename R>
    std::vector<R> find_values_in_bools(const z3::expr &expr, const std::function<std::optional<R>(const z3::expr &)> &predicate, bool search_in_success = false, bool search_in_failed = true) {
        return find_values_where<R>(
                expr,
                [&](const z3::expr &e) -> std::optional<R> {
                    if(e.is_bool())
                        return predicate(e);
                    return {};
                },
                [&](z3::expr e, std::optional<R> r){ return e.is_bool() && (r ? search_in_success : search_in_failed); }
        );
    }

    /**
     * Recursively traverses the given expression, conditionally collecting some of them.
     *
     * @param expr The expression to traverse
     * @param predicate Determines, for a given sub-expression, whether to include it in the result
     * @param recurse A predicate to determine whether to traverse the sub-tree of a given expression, given the current
     *                expression and the result from "predicate" for that expression.
     * @return All expressions for which "predicate" returned true
     */
    std::vector<z3::expr> find_where(const z3::expr &expr, const std::function<bool(const z3::expr &)> &predicate, const std::function<bool(const z3::expr &, bool)> &recurse);

    /**
     * Recursively traverses the given expression, conditionally collecting some of them.
     *
     * @param expr The expression to traverse
     * @param predicate Determines, for a given sub-expression, whether to include it in the result
     * @param search_in_success Whether to traverse the sub-tree if "predicate" returned true for a given expression
     *                          (skipped by default).
     * @param search_in_failed Whether to traverse the sub-tree if "predicate" returned false for a given expression
     *                         (true by default).
     * @return All expressions for which "predicate" returned true
     */
    std::vector<z3::expr> find(const z3::expr &expr, const std::function<bool(const z3::expr &)> &predicate, bool search_in_success = false, bool search_in_failed = true);

    /**
     * Recursively traverses the given boolean-sorted parts of the expression, conditionally collecting some of them.
     *
     * @param expr The expression to traverse
     * @param predicate Determines, for a given sub-expression of sort bool, whether to include it in the result
     * @param search_in_success Whether to traverse the sub-tree if "predicate" returned true for a given expression
     *                          (skipped by default).
     * @param search_in_failed Whether to traverse the sub-tree if "predicate" returned false for a given expression
     *                         (true by default).
     * @return All expressions for which "predicate" returned true
     */
    std::vector<z3::expr> find_bools(const z3::expr &expr, const std::function<bool(const z3::expr &)> &predicate, bool search_in_success = false, bool search_in_failed = true);

    /**
     * Returns a new expression with all occurrences of "to_be_replaced" replaced by "replacement".
     *
     * @param expr The expression in which to perform the substitution
     * @param to_be_replaced The expression to be replaced
     * @param replacement The expression replacing the current value
     * @return The expression with the substitution applied
     */
    z3::expr substitute(const z3::expr &expr, const z3::expr &to_be_replaced, const z3::expr &replacement);

    /**
     * Returns a new expression, for each pair replacing all occurrences of the first expression
     * with the second expression.
     *
     * @param expr The expression in which to perform the substitution
     * @param replacements A range of pairs<expr,expr>, where each first element is the expression
     *                     to be replaced, and each second element the respective replacement.
     * @return The expression with the substitutions applied
     */
    template <std::ranges::range R>
    requires std::convertible_to<std::ranges::range_value_t<R>, std::pair<z3::expr,z3::expr>>
    z3::expr substitute_all(const z3::expr &expr, R&& replacements) {
        z3::ast_vector_tpl<z3::expr> src { expr.ctx() };
        z3::ast_vector_tpl<z3::expr> dst { expr.ctx() };

        for(const std::pair<z3::expr,z3::expr> r : replacements) {
            src.push_back(r.first);
            dst.push_back(r.second);
        }

        z3::expr copy = expr;
        return copy.substitute(src, dst);
    }

    /**
     * Returns a new expression, replacing all of the given expressions with a replacement, generated by
     * the given mapping function.
     *
     * @param expr The expression in which to perform the substitution
     * @param to_be_replaced A range of expressions to be replaced
     * @param mapping A function, applied once for each expression from to_be_replaced, to generate the replacements
     *                for the given expressions
     * @return The expression with the substitutions applied
     */
    template <std::ranges::range R>
    requires std::convertible_to<std::ranges::range_value_t<R>, z3::expr>
    z3::expr substitute_all(const z3::expr &expr, R&& to_be_replaced, const std::function<z3::expr(const z3::expr &)> &mapping) {
        return substitute_all(expr, to_be_replaced | std::views::transform([&](const z3::expr &t) -> std::pair<z3::expr,z3::expr> { return { t, mapping(t) }; }));
    }

    /**
     * Removes any if-then-else expressions from the given expression, by replacing them with regular boolean
     * conditions. Since these replacements can't necessarily be done directly where the ITE is located in the
     * expression (when it is not of sort bool), the given expression itself must be of sort bool.
     *
     * @param expr A boolean-sorted expression to replace any ITEs in
     * @return An equivalent expression without any ITEs
     */
    z3::expr replace_ite(const z3::expr &expr);

    /**
     * Performs variable inlining at best-effort basis. E.g. (x + 1 = 0 && exp(x,y)) may be replaced with
     * (x = -1 && exp(-1,y)), but not too much effort will be spent trying to rearrange an equality to result
     * in a constant term. Note that all variables will remain in the formula, but possibly only in an
     * occurrence (var = constant). There is no need to invoke this method several times, it already internally
     * performs transitive inlining.
     *
     * @param expr The expression in which to inline constant
     * @return The expression with some variables inlined
     */
    z3::expr inline_constants(const z3::expr &expr);

    /**
     * Creates a range reduction operation that returns AND{r in range} for a given range,
     * returning "true" if the range is empty.
     *
     * @param ctx An expression used as context. The actual expression is irrelevant.
     */
    logic_reduction<true> reduce_and(const z3::expr &ctx);

    /**
     * Creates a range reduction operation that returns OR{r in range} for a given range,
     * returning "false" if the range is empty.
     *
     * @param ctx An expression used as context. The actual expression is irrelevant.
     */
    logic_reduction<false> reduce_or(const z3::expr &ctx);

    /**
     * Compares the given two expressions under the specified interpretation. If they have identical values
     * in the interpretation, the to_string() values will be compared.
     *
     * @param interpretation The interpretation under which to compare the two expressions
     * @param a The first expression, must evaluate to a numeral under the interpretation
     * @param b The second expression, must also evaluate to a numeral under the interpretation
     * @return A negative int, 0, or a positive int if a is less than, equal to, or greater than b
     */
    int cmp_in_interp(const z3::model &interpretation, const z3::expr &a, const z3::expr &b);

    /**
     * Computes floor(log_base(x)).
     *
     * @param x The value to compute the logarithm of
     * @param base The base for the log function
     * @return floor(log_base(x))
     */
    cpp_int floor_log(const cpp_int &x, const cpp_int &base);

    /**
     * Computes ceil(log_base(x)).
     *
     * @param x The value to compute the logarithm of
     * @param base The base for the log function
     * @return ceil(log_base(x))
     */
    cpp_int ceil_log(const cpp_int &x, const cpp_int &base);

    /**
     * Computes log_base(x), if the result would be an integer, otherwise it returns
     * an empty optional.
     *
     * @param x The value to compute the logarithm of
     * @param base The base for the log function
     * @return log_base(x) if the result is exactly an integer, otherwise an empty optional
     */
    std::optional<cpp_int> log_exact(const cpp_int &x, const cpp_int &base);

    /**
     * Computes exp(base, abs(exp)).
     *
     * @param base The base for the exponential function
     * @param exp The exponent to raise by the base
     * @return exp(base, abs(exp))
     */
    cpp_int abs_pow(const cpp_int &base, const cpp_int &exp);

    /**
     * Combines two exp bases into a common base, into the first variable. Each base,
     * and the output, can have 3 cases:
     * <ul>
     *   <li>0: No exp -> no base, but not conflicting</li>
     *   <li>>0: That value is the base</li>
     *   <li>{}: Several non-equal bases</li>
     * </ul>
     *
     * @param base The first base. This is where the output will be written into
     * @param base2 The second base
     * @return True iff the bases don't conflict, false otherwise
     */
    bool join_common_base(std::optional<cpp_int> &base, const std::optional<cpp_int> &base2);
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

    /** Variable counter, to keep generated variables unique */
    unsigned int var_counter = 0;

public:

    /**
     * SwInE config
     */
    const Config &config;
    /**
     * Reference to Swine.statistics, which may be updated accordingly.
     */
    Statistics &stats;
    /**
     * Z3 context of all expressions.
     */
    z3::context &ctx;
    /**
     * Function declaration for the Int exp(Int,Int) function.
     */
    std::unique_ptr<z3::func_decl> exp;
    /**
     * The common base to use with all exponential operations that don't take
     * a base as parameter.
     */
    cpp_int base {0};

    Util(z3::context &ctx, const Config &config, Statistics &stats);

    /**
     * Converts the given number to a Z3 expression.
     *
     * @param value The numeric value for the expression
     * @return A z3::expr with the same numeric value of sort int
     */
    z3::expr term(const cpp_int &value) const;

    /**
     * Creates the expression exp(base, exponent).
     *
     * @param base The first argument for the exp call
     * @param exponent The second argument for the exp call
     * @return The exp expression
     */
    z3::expr make_exp(const z3::expr &base, const z3::expr &exponent) const;

    /**
     * Creates the expression exp(base, exponent), where base is the configured common base.
     *
     * @param exponent The second argument for the exp call
     * @return The exp expression
     */
    z3::expr make_exp(const z3::expr &exponent) const;

    /**
     * Converts a bool to an Z3 expression.
     *
     * @param value The bool value
     * @return The value as an expression
     */
    z3::expr bool_expr(const bool value) const;

    /**
     * @return The bool expression "true"
     */
    z3::expr top() const;

    /**
     * @return The bool expression "false"
     */
    z3::expr bot() const;

    /**
     * Creates a new variable.
     *
     * @return A Z3 expression representing a fresh variable
     */
    z3::expr new_variable();

    /**
     * Creates a new Z3 symbol.
     *
     * @return A fresh Z3 symbol that may be used to create a fresh variable, function etc.
     */
    z3::symbol new_symbol();

    /**
     * Creates a range reduction operation that returns AND{r in range} for a given range,
     * returning "true" if the range is empty.
     */
    logic_reduction<true> reduce_and() const;

    /**
     * Creates a range reduction operation that returns OR{r in range} for a given range,
     * returning "false" if the range is empty.
     */
    logic_reduction<false> reduce_or() const;

    /**
     * Computes floor(log(x)) for the configured common base.
     *
     * @param x The value to compute the logarithm of
     * @return floor(log(x))
     */
    cpp_int floor_log(const cpp_int &x) const;

    /**
     * Computes ceil(log(x)) for the configured common base.
     *
     * @param x The value to compute the logarithm of
     * @return ceil(log(x))
     */
    cpp_int ceil_log(const cpp_int &x) const;

    /**
     * Computes log(x), if the result would be an integer, otherwise it returns an empty
     * optional.
     *
     * @param x The value to compute the logarithm of
     * @return log(x) if the result is exactly an integer, otherwise an empty optional
     */
    std::optional<cpp_int> log_exact(const cpp_int &x) const;

    /**
     * Computes exp(abs(x)) for the configured common base.
     *
     * @param exponent The value to raise by the common base
     * @return exp(abs(x))
     */
    cpp_int abs_pow(const cpp_int &exponent) const;
};

}

namespace range_utils {
    // Special implementation of to<expr_set>()
    template <std::ranges::range R>
    swine::expr_set operator|(R&& r, collector<swine::expr_set>) {
        swine::expr_set res;
        for(const z3::expr &e : r)
            res.add(e);
        return res;
    }
}
