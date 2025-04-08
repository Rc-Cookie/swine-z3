#include "stats.h"

namespace swine {

    using namespace std::chrono;

    void Statistics::reset() {
        iterations = 0;
        symmetry_lemmas = 0;
        bounding_lemmas = 0;
        prime_lemmas = 0;
        interpolation_lemmas = 0;
        monotonicity_lemmas = 0;
        induction_lemmas = 0;
        eia_n_lemmas = 0;
        num_assertions = 0;
        non_constant_base = false;
        algorithm = Algorithm::None;
    }

    std::string algorithm::str(const Algorithm algorithm) {
        switch(algorithm) {
            case Algorithm::None: return "None";
            case Algorithm::Z3: return "Z3";
            case Algorithm::Lemmas: return "Lemmas";
            case Algorithm::EIAProj: return "EIAProj";
            case Algorithm::EIA: return "EIA";
        }
        throw std::invalid_argument("Unknown algorithm");
    }

    bool algorithm::produces_model(const Algorithm a) {
        return a == Algorithm::Z3 || a == Algorithm::Lemmas;
    }

    std::ostream& operator<<(std::ostream &s, const Algorithm algorithm) {
        return s << algorithm::str(algorithm);
    }

    std::ostream& operator<<(std::ostream &s, const Statistics &stats) {
        s <<   "assertions           : " << stats.num_assertions;
        s << "\niterations           : " << stats.iterations;
        s << "\nsymmetry lemmas      : " << stats.symmetry_lemmas;
        s << "\nbounding lemmas      : " << stats.bounding_lemmas;
        s << "\nmonotonicity lemmas  : " << stats.monotonicity_lemmas;
        s << "\nprime lemmas         : " << stats.prime_lemmas;
        s << "\ninduction lemmas     : " << stats.induction_lemmas;
        s << "\ninterpolation lemmas : " << stats.interpolation_lemmas;
        s << "\neia-n lemmas         : " << stats.eia_n_lemmas;
        s << "\nnon constant base    : " << (stats.non_constant_base ? "true" : "false");
        s << "\nalgorithm            : " << stats.algorithm;
        return s;
    }
}
