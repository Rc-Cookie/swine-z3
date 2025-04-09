#include "algorithm.h"
#include <stdexcept>

namespace swine {

    std::string algorithm::str(const Algorithm algorithm) {
        switch(algorithm) {
            case Algorithm::Z3: return "z3";
            case Algorithm::Lemmas: return "lemmas";
            case Algorithm::EIAProj: return "eia-proj";
            case Algorithm::EIA: return "eia-iter";
        }
        throw std::invalid_argument("Unknown algorithm");
    }

    bool algorithm::produces_model(const Algorithm a) {
        return a == Algorithm::Z3 || a == Algorithm::Lemmas;
    }

    std::ostream& operator<<(std::ostream &s, const Algorithm algorithm) {
        return s << algorithm::str(algorithm);
    }
}
