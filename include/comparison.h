#pragma once

#include <z3++.h>
#include <boost/multiprecision/cpp_int.hpp>
#include "util.h"
#include "term.h"

namespace swine {

    using namespace boost::multiprecision;

    /**
     * Represents a normalized comparison of an integral term with 0. Three different kinds of comparisons are
     * supported:
     * <ul>
     *   <li>Equality: t = 0</li>
     *   <li>Inequality (not equals): t != 0</li>
     *   <li>Inequality (strictly less than): t < 0. But all kinds of inequalities (<,<=,>,>=) will be parsed
     *   and converted to this format (we can convert t <= 0 to t-1 < 0 with integers).</li>
     * </ul>
     */
    struct Comparison {

        /**
         * The relation of the term with the constant 0.
         */
        enum class Kind {
            /** The term should be equal to 0. */
            Equal,
            /** The term should not be equal to 0. */
            NotEqual,
            /** The term should be (strictly) less than 0. */
            Less
        };

        /** The term compared to 0. */
        Term term;
        /** The relation of the term with the term 0. */
        Kind kind;
        /**
         * The expression that this comparison was parsed from (before normalization). The value will
         * only be valid when the comparison was constructed via parse, try_parse or via the Comparison(expr)
         * constructor. Upon further modifications this expression will NOT be updated accordingly.
         */
        z3::expr original;

        /**
         * Converts a Z3 expression into a comparison, throwing an exception if it does not represent a comparison.
         * The "original" field will be set to the given expression.
         *
         * @param comparison The expression to parse
         */
        Comparison(const z3::expr &comparison);

        /**
         * Creates a comparison with the given term and the specified relation to 0. The "original" field
         * will be generated from the term and the kind of comparison.
         *
         * @param term The term in relation to 0
         * @param kind The relation of the term to the value 0
         */
        Comparison(const Term &term, Kind kind);

        /**
         * Creates a comparison with the given term, its relation to 0 and the specified value for the
         * "original" field. The value of "original" will NOT be validated, in that it is actually equivalent
         * to the term and kind or comparison.
         *
         * @param term The term in relation to 0
         * @param kind The relation of the term to the value 0
         * @param original The value for the "original" field
         */
        Comparison(const Term &term, Kind kind, const z3::expr &original);

        /**
         * Converts this comparison back to a Z3 expression in a normalized format (i.e. not the value of
         * "original").
         *
         * @return An equivalent Z3 expression
         */
        z3::expr normalized() const;

        /**
         * Determines whether this comparison is within the extended "PowerComp" fragment, that means, it
         * is equivalent to one of the following terms:
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
         * where x,y are variables and a,b are non-zero constants.
         *
         * @return Whether this comparison is equivalent to a comparison from the extended PowerComp fragment
         */
        bool is_in_power_comp() const;

        /**
         * Logically negates this comparison in-place, that is, it will be true iff it was false before.
         * E.g. t = 0 would become t != 0, and t < 0 would become t >= 0, or in other words, -t - 1 < 0.
         * Note that this operation will NOT update the "original" expression.
         */
        void negate();

        /**
         * Tests whether the homogeneous part of this comparison (which is exactly the homogeneous part of
         * its term) is identical to the one in the given comparison. Note that in particular, this does
         * NOT compare the kinds of the comparisons (because any kind of comparison can be expressed a set
         * of strict inequalities only modifying the term's constant, so the homogeneous part would stay
         * identical).
         *
         * @param c The comparison to compare
         * @return True iff the homogeneous part of this comparison's term is equal to the given comparison's
         *         homogeneous term part
         */
        const bool homogeneous_equals(const Comparison &c) const;

        /**
         * Attempts to parse and normalized the given Z3 expression into a comparison.
         *
         * @param comparison The expression to parse
         * @return The parsed comparison, or an empty optional if it could not be parsed
         */
        static std::optional<Comparison> try_parse(const z3::expr &comparison);

        /**
         * Parses and normalizes the given Z3 expression into a comparison, throwing an exception if
         * the expression does not represent a valid comparison.
         *
         * @param comparison The expression to parse
         * @return The parsed comparison
         */
        static Comparison parse(const z3::expr &comparison) {
            std::optional<Comparison> c = try_parse(comparison);
            if(!c)
                throw z3::exception("Invalid comparison");
            return *c;
        }

        /**
         * Groups the given range of comparisons into groups which all share the same homogeneous
         * part, according to homogeneous_equals(). In particular, this means that one group may
         * contain different kinds of comparisons, if they still share the same homogeneous term
         * part.
         *
         * @tparam R A range of comparisons
         * @param comparisons The comparisons to groups
         * @return A list of groups, for each group it mutually holds that a.homogeneous_equals(b)
         *         and between different groups mutually the opposite. The groups and group contents
         *         are in no particular order.
         */
        template <std::ranges::range R>
        requires std::convertible_to<std::ranges::range_value_t<R>, Comparison>
        static std::vector<std::vector<Comparison>> group_by_homogeneous(R && comparisons) {

            std::vector<std::vector<Comparison>> groups;

            for(const Comparison &c : comparisons) {
                for(std::vector<Comparison> &group : groups) {
                    if(group.at(0).homogeneous_equals(c)) {
                        group.push_back(c);
                        goto outer;
                    }
                }
                groups.push_back({ c });
                outer:;
            }

            return groups;
        }

        /**
         * Calculates the 1-norm of the given comparison. This is very similar to the 1-norm of the
         * underlying term, but may differ by +-1, as the 1-norm of a comparison is originally only
         * defined for strict inequalities, and thus, any other comparison kinds are implicitly
         * converted to strict inequalities first, possibly introducing a constant offset of +-1.
         *
         * @param c The comparison to calculate the 1-norm of
         * @return The comparison's 1-norm
         */
        static const cpp_int one_norm(const Comparison &c);

        /**
         * Converts this comparison to a string, based on Term::to_string().
         *
         * @return A string representation (not smt2 format!) of this comparison
         */
        std::string to_string() const;
    };

    std::ostream& operator<<(std::ostream &s, const Comparison::Kind &k);
    std::ostream& operator<<(std::ostream &s, const Comparison &c);
}
