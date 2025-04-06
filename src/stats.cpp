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
        num_assertions = 0;
        non_constant_base = false;
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
        s << "\nnon constant base    : " << (stats.non_constant_base ? "true" : "false");
        return s;
    }
}
