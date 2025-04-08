#pragma once

#include <optional>
#include <chrono>
#include <unordered_set>
#include <boost/multiprecision/cpp_int.hpp>

namespace swine {

    /**
     * A simple class to track the duration of something. Counts the time starting
     * from initialization time.
     */
    class Timer {

        std::chrono::system_clock::time_point start { std::chrono::system_clock::now() };

    public:

        using duration = std::chrono::system_clock::duration;

        /**
         * @return The duration since the last reset, or since initialization if never reset
         */
        duration get() const {
            return std::chrono::system_clock::now() - start;
        }

        /**
         * Resets the timer and returns the time until that reset.
         *
         * @return The duration since the previous reset, or since initialization if this was
         *         the first reset
         */
        duration get_and_reset() {
            const std::chrono::system_clock::time_point now = std::chrono::system_clock::now();
            const duration diff = now - start;
            start = now;
            return diff;
        }

        /**
         * Equivalent to get().
         *
         * @return The duration since the last reset, or since initialization if never reset
         */
        operator duration() const {
            return get();
        }
    };

    /**
     * Possible solving algorithms.
     */
    enum class Algorithm {
        /** Default value */
        None,
        /** Just regular Z3 - the formula did not contain any exp() expressions (after preprocessing) */
        Z3,
        /** Incremental lemma generation */
        Lemmas,
        /** Approximation-based complete algorithm for the EIA_n fragment */
        EIAProj,
        /** Non-lazy version of the complete algorithm for the EIA_n fragment (with some feasibility optimizations) */
        EIA
    };

    namespace algorithm {
        /** Returns the name of the enum constant. */
        std::string str(const Algorithm a);

        /** Whether the given algorithm is capable of producing a model, if it proves a formula satisfiable. */
        bool produces_model(const Algorithm a);
    }

    /**
     * Tracks statistics about the SwInE solver.
     */
    struct Statistics {

        /** The number of iterations performed. */
        unsigned int iterations {0};
        /** The number of symmetry lemmas used. */
        unsigned int symmetry_lemmas {0};
        /** The number of bounding lemmas used. */
        unsigned int bounding_lemmas {0};
        /** The number of prime lemmas used. */
        unsigned int prime_lemmas {0};
        /** The number of interpolation lemmas used. */
        unsigned int interpolation_lemmas {0};
        /** The number of monotonicity lemmas used. */
        unsigned int monotonicity_lemmas {0};
        /** The number of induction lemmas used. */
        unsigned int induction_lemmas {0};
        /** The number of EIA_n projection lemmas used. */
        unsigned int eia_n_lemmas {0};
        /** The number of assertions added using Swine::add(). */
        unsigned int num_assertions {0};
        /** Whether any exp() expression had a non-constant term as base, after preprocessing. */
        bool non_constant_base {false};
        /** Whether any exp() expression had a non-constant term as base, after preprocessing. */
        Algorithm algorithm {Algorithm::None};

        /** Resets all counters to 0 / their respective default state. */
        void reset();
    };

    std::ostream& operator<<(std::ostream &s, const Algorithm algorithm);

    std::ostream& operator<<(std::ostream &s, const Statistics &stats);
}
