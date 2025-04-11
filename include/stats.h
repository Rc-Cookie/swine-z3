#pragma once

#include <optional>
#include <chrono>
#include <unordered_set>
#include <boost/multiprecision/cpp_int.hpp>
#include "algorithm.h"
#include "lemma_kind.h"

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
         * Resets the timer to 0.
         */
        void reset() {
            start = std::chrono::system_clock::now();
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
     * Statistics about the duration spent in several parts of the solver.
     */
    struct Timings {

        using duration = Timer::duration;

        /** Time spent transforming the input formula and populating caches. */
        duration preprocessing {0};
        /** Time spent during preprocessing for detecting a common exp() base. */
        duration base_detection {0};
        /** Time spent actually solving. */
        duration solving {0};
        /** Time spent solving with each algorithm. If an algorithm is not present, it's implicitly 0. */
        std::unordered_map<Algorithm, duration> algorithms;
        /** Time spent in the "lemmas" algorithm generating approximations with Z3. */
        duration lemmas_approximate {0};
        /** Time spent generating each kind of lemma. If a kind is not present, it's implicitly 0. */
        std::unordered_map<LemmaKind, duration> lemmas;
        /** Time spent in the "eia-proj" algorithm generating approximations with Z3. */
        duration eia_proj_approximate {0};
        /** Time spent in the "eia-proj" algorithm eliminating variables with model based projection. */
        duration eia_proj_mbp {0};
        /** Time spent in the "eia-proj" algorithm in the AbSimplifyDiv procedure. */
        duration eia_proj_simplify_div {0};
        /** Time spent in the "eia-proj" algorithm in the AbSemCover procedure. */
        duration eia_proj_sem_cover {0};
        /** Time spent in the "eia-proj" algorithm linearizing formulas from PowerComp. */
        duration eia_proj_linearize {0};
        /** Time spent in the "eia-iter" algorithm eliminating variables with Z3 quantifier elimination. */
        duration eia_iter_qe {0};
        /** Time spent in the "eia-iter" algorithm in the SimplifyDiv procedure. */
        duration eia_iter_simplify_div {0};
        /** Time spent in the "eia-iter" algorithm in the SemCover procedure (without linearization). */
        duration eia_iter_sem_cover {0};
        /** Time spent in the "eia-iter" algorithm's SemCover procedure checking feasibility of sub-formulas. */
        duration eia_iter_feasibility {0};
        /** Time spent in the "eia-iter" algorithm linearizing formulas from PowerComp */
        duration eia_iter_linearize {0};
        /** Time spent validating sat/unsat results. Considered part of the solver time. */
        duration validation {0};

        /** Returns the duration spent on the given algorithm. */
        duration algorithm(Algorithm a) const;

        /** Increments the time spent on the given algorithm by the specified amount. */
        duration add_to_algorithm(Algorithm a, const duration &dt);

        /** Returns the duration spent generating the given kind of lemmas. */
        duration lemma(LemmaKind k) const;

        /** Increments the time spent generating the given kind of lemmas by the specified amount. */
        duration add_to_lemma(LemmaKind k, const duration &dt);

        /** Returns the sum of the durations, excluding sub-durations. */
        duration total() const;

        Timings& operator+=(const Timings &dt);

        Timings operator+(const Timings &t2) const;
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
        /** Durations of certain parts of the solving process. */
        Timings timings;
    };

    std::ostream& operator<<(std::ostream &s, const Timings &timings);
    std::ostream& operator<<(std::ostream &s, const Statistics &stats);
}
