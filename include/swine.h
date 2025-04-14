#pragma once

#include "config.h"
#include "stats.h"
#include "eia_proj.h"

#include <z3++.h>
#include <boost/multiprecision/cpp_int.hpp>
#include <unordered_set>
#include <optional>

namespace swine {

class Util;

std::ostream& operator<<(std::ostream &s, const LemmaKind kind);

class ExpGroup;
class Preprocessor;
class ExpFinder;

class Swine {

private:

    struct Frame {
        z3::expr_vector exps;
        std::unordered_set<unsigned> exp_ids;
        std::vector<std::shared_ptr<ExpGroup>> exp_groups;
        // mapping from assumption literals to the corresponding formulas for unsat cores
        std::vector<std::pair<z3::expr, z3::expr>> assumptions;
        z3::expr_vector assertions;
        // mapping from preprocessed to original assertions
        std::vector<std::pair<z3::expr, z3::expr>> preprocessed_assertions;
        std::unordered_map<unsigned, LemmaKind> lemma_kinds;
        expr_set lemmas;
        std::unordered_map<unsigned, z3::expr_vector> bounding_lemmas;
        bool assert_failed {false};

        Frame(z3::context &ctx);

    };

    struct EvaluatedExponential {
        z3::expr exp_expression;
        boost::multiprecision::cpp_int exp_expression_val;
        boost::multiprecision::cpp_int expected_val;
        z3::expr base;
        boost::multiprecision::cpp_int base_val;
        z3::expr exponent;
        long long exponent_val;

        EvaluatedExponential(const z3::expr &exp_expression);

    };

    friend std::ostream& operator<<(std::ostream &s, const EvaluatedExponential &exp);

    struct Interpolant {
        z3::expr t;
        boost::multiprecision::cpp_int factor;

        Interpolant(const z3::expr &t);

    };

    Statistics stats;
    const Config config;
    z3::context &ctx;
    z3::solver solver;
    std::unique_ptr<Util> util;
    std::vector<Frame> frames;
    std::unordered_map<unsigned, std::vector<std::pair<boost::multiprecision::cpp_int, long long>>> interpolation_points;
    std::unique_ptr<Preprocessor> preproc;
    std::unique_ptr<ExpFinder> exp_finder;
    bool sat_mode {true};
    long long bound {2};
    z3::model model;
    std::unique_ptr<EIAProj> eia_proj;

    friend std::ostream& operator<<(std::ostream &s, const Swine &swine);

    z3::check_result check(z3::expr_vector assumptions);
    z3::check_result check(Algorithm algorithm);
    z3::check_result check_with_z3();
    z3::check_result check_with_eia_n_proj();
    z3::check_result check_with_eia_n();
    z3::check_result check_with_lemmas();
    void generate_lemmas(LemmaKind kind, std::vector<std::pair<z3::expr, LemmaKind>> &dst);
    void base_symmetry_lemmas(const z3::expr &e, z3::expr_vector &lemmas);
    void exp_symmetry_lemmas(const z3::expr &e, z3::expr_vector &lemmas);
    void symmetry_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    void compute_bounding_lemmas(const ExpGroup &g);
    void bounding_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    EvaluatedExponential evaluate_exponential(const z3::expr &exp_expression) const;
    Interpolant interpolate(const z3::expr &t, const unsigned pos, const boost::multiprecision::cpp_int x1, const boost::multiprecision::cpp_int x2);
    z3::expr interpolation_lemma(const z3::expr &t, const bool upper, const std::pair<boost::multiprecision::cpp_int, long long> a, const std::pair<boost::multiprecision::cpp_int, long long> bx2);
    void interpolation_lemma(const EvaluatedExponential &e, std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    void interpolation_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    z3::expr_vector tangent_refinement(const z3::expr &exponent1, const z3::expr &exponent2, const z3::expr &expected1, const z3::expr &expected2);
    std::optional<z3::expr> induction_lemma(EvaluatedExponential e1, EvaluatedExponential e2);
    void induction_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    std::optional<z3::expr> monotonicity_lemma(const EvaluatedExponential &e1, const EvaluatedExponential &e2);
    void monotonicity_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    void prime_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    void eia_n_lemmas(std::vector<std::pair<z3::expr, LemmaKind>> &lemmas);
    void verify();
    void brute_force();
    void add_lemma(const z3::expr &lemma, const LemmaKind kind);
    void preprocess_lemmas(const std::vector<std::pair<z3::expr, LemmaKind>> &lemmas, std::vector<std::pair<z3::expr, LemmaKind>> &dst);
    z3::expr get_value(const z3::expr &exp) const;
    void add_bounds();

public:

    Swine(const Config &config, z3::context &ctx);
    ~Swine();
    void add(const z3::expr & t);
    z3::check_result check();
    void push();
    void pop();
    bool has_model() const;
    z3::model get_model() const;
    void reset();
    z3::context& get_ctx();
    z3::func_decl& get_exp();
    z3::solver& get_solver();
    const z3::solver& get_solver() const;
    const Statistics& get_stats() const;

};

std::ostream& operator<<(std::ostream &s, const Swine &swine);

}
