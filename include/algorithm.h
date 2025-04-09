#pragma once

#include <string>
#include <optional>
#include <unordered_set>

namespace swine {

    /**
     * Possible solving algorithms.
     */
    enum class Algorithm {
        /** Just regular Z3 - the formula did not contain any exp() expressions (after preprocessing) */
        Z3,
        /** Incremental lemma generation */
        Lemmas,
        /** Approximation-based complete algorithm for the EIA_n fragment */
        EIAProj,
        /** Non-lazy version of the complete algorithm for the EIA_n fragment (with some feasibility optimizations) */
        EIA
    };

    /**
     * Functions related to swine::Algorithm
     */
    namespace algorithm {

        /** All swine::Algorithm constants */
        static const std::unordered_set<Algorithm> values {Algorithm::Z3,
                                                           Algorithm::Lemmas,
                                                           Algorithm::EIAProj,
                                                           Algorithm::EIA};

        /** Returns the name of the enum constant. */
        std::string str(const Algorithm a);

        /** Whether the given algorithm is capable of producing a model, if it proves a formula satisfiable. */
        bool produces_model(const Algorithm a);
    }

    std::ostream& operator<<(std::ostream &s, const Algorithm algorithm);
}
