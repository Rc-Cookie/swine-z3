#pragma once

#include <optional>
#include <chrono>
#include <unordered_set>
#include <boost/multiprecision/cpp_int.hpp>
#include "algorithm.h"

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
        /** The algorithms used for solving. */
        std::optional<Algorithm> algorithm {};

        /** Resets all counters to 0 / their respective default state. */
        void reset();
    };

    std::ostream& operator<<(std::ostream &s, const Statistics &stats);
}
