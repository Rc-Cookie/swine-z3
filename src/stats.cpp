#include "stats.h"

namespace swine {

    using namespace std::chrono;


    Timings::duration Timings::algorithm(Algorithm a) const {
        const auto it = algorithms.find(a);
        return it == algorithms.end() ? Timings::duration::zero() : it->second;
    }

    Timings::duration Timings::add_to_algorithm(Algorithm a, const Timings::duration &dt) {
        return algorithms[a] += dt;
    }

    Timings::duration Timings::lemma(LemmaKind k) const {
        const auto it = lemmas.find(k);
        return it == lemmas.end() ? Timings::duration::zero() : it->second;
    }

    Timings::duration Timings::add_to_lemma(LemmaKind k, const Timings::duration &dt) {
        return lemmas[k] += dt;
    }

    Timings::duration Timings::total() const {
        return preprocessing + solving;
    }

    Timings& Timings::operator+=(const Timings &dt) {
        preprocessing += dt.preprocessing;
        base_detection += dt.base_detection;
        solving += dt.solving;
        for(const auto &[a,t] : dt.algorithms)
            add_to_algorithm(a,t);
        lemmas_approximate += dt.lemmas_approximate;
        for(const auto &[k,t] : dt.lemmas)
            add_to_lemma(k,t);
        eia_proj_approximate += dt.eia_proj_approximate;
        eia_proj_mbp += dt.eia_proj_mbp;
        eia_proj_simplify_div += dt.eia_proj_simplify_div;
        eia_proj_sem_cover += dt.eia_proj_sem_cover;
        eia_proj_linearize += dt.eia_proj_linearize;
        eia_iter_qe += dt.eia_iter_qe;
        eia_iter_simplify_div += dt.eia_iter_simplify_div;
        eia_iter_sem_cover += dt.eia_iter_sem_cover;
        eia_iter_feasibility += dt.eia_iter_feasibility;
        eia_iter_linearize += dt.eia_iter_linearize;
        validation += dt.validation;
        return *this;
    }

    Timings Timings::operator+(const swine::Timings &t2) const {
        Timings res = *this;
        res += t2;
        return res;
    }

    std::ostream& line(std::ostream &s, const std::string &label, const Timings::duration &duration, bool newline = true) {
        const size_t minWidth = 20;
        const size_t width = label.length();
        if(newline)
            s << '\n';
        s << label;
        if(minWidth > width)
            s << std::string(minWidth - width, ' ');
        return s << " : " << duration_cast<milliseconds>(duration).count() << " ms";
    }

    std::ostream& operator<<(std::ostream &s, const Timings &timings) {
        line(s, "preprocessing",    timings.preprocessing, false);
        line(s, "- base detection", timings.base_detection);
        line(s, "solving",          timings.solving);
        for(Algorithm a : algorithm::values) {
            if(!timings.algorithms.contains(a))
                continue;
            line(s, "- " + algorithm::str(a), timings.algorithms.at(a));
            switch(a) {
                case Algorithm::Lemmas: {
                    line(s, "  - approximation", timings.lemmas_approximate);
                    for(LemmaKind k : lemma_kind::values)
                        line(s, "  - " + lemma_kind::str(k), timings.lemma(k));
                    break;
                }
                case Algorithm::EIAProj: {
                    line(s, "  - approximation", timings.eia_proj_approximate);
                    line(s, "  - mbp", timings.eia_proj_mbp);
                    line(s, "  - simplify div", timings.eia_proj_simplify_div);
                    line(s, "  - sem cover", timings.eia_proj_sem_cover);
                    line(s, "  - linearize", timings.eia_proj_linearize);
                    break;
                }
                case Algorithm::EIA: {
                    line(s, "  - qe", timings.eia_iter_qe);
                    line(s, "  - simplify div", timings.eia_iter_simplify_div);
                    line(s, "  - sem cover", timings.eia_iter_sem_cover);
                    line(s, "    - feasibility", timings.eia_iter_feasibility);
                    line(s, "  - linearize", timings.eia_iter_linearize);
                    break;
                }
                default: break;
            }
        }
        if(timings.validation.count())
            line(s, "- validation", timings.validation);
        return line(s, "check()", timings.total());
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
        s << "\nalgorithm            : " << (stats.algorithm ? algorithm::str(*stats.algorithm) : "none");
        s << "\ntimings:\n" << stats.timings;
        return s;
    }
}
