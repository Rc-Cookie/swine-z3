#include "swine.h"
#include "version.h"
#include "lemma_kind.h"
#include "preproc_kind.h"
#include "config.h"

#include <boost/algorithm/string.hpp>
#include <z3++.h>

using namespace swine;

void version() {
    std::cout << "Build SHA: " << Version::GIT_SHA << " (" << Version::GIT_DIRTY << ")" << std::endl;
}

void argument_parsing_failed(const std::string &str) {
    throw std::invalid_argument("extra argument " + str);
}

void print_help() {
    const auto length {std::string("  --no-constant-folding").length()};
    std::cout << std::endl;
    std::cout << "***** SwInE Z3 -- SMT with Integer Exponentiation *****" << std::endl;
    std::cout << std::endl;
    std::cout << "usage: swine [args] input.smt2" << std::endl;
    std::cout << std::endl;
    std::cout << "valid arguments:" << std::endl;
    for (const auto k: lemma_kind::values) {
        const auto str {std::string("  --no-") + lemma_kind::str(k)};
        const auto ws {length - str.length()};
        std::cout << str << std::string(ws, ' ') << " : disable " << k << " lemmas" << std::endl;
    }
    for (const auto k: preproc_kind::values) {
        const auto str {std::string("  --no-") + preproc_kind::str(k)};
        const auto ws {length - str.length()};
        std::cout << str << std::string(ws, ' ') << " : disable " << k << std::endl;
    }
    std::cout << "  --validate-sat        : validate SAT results by evaluating the input w.r.t. solution" << std::endl;
    std::cout << "  --validate-unsat c    : validate UNSAT results by forcing exponents to values in {0,...,c}, c in IN" << std::endl;
    std::cout << "  --no-phasing          : disable phasing" << std::endl;
    std::cout << "  --get-lemmas          : print all lemmas that were used in the final proof if UNSAT is proven, or all lemmas if SAT is shown" << std::endl;
    std::cout << "  --stats               : print statistics in the end" << std::endl;
    std::cout << "  --help                : print this text and exit" << std::endl;
    std::cout << "  --version             : print the SwInE version and exit" << std::endl;
    std::cout << "  --no-version          : omit the SwInE version at the end of the output" << std::endl;
    std::cout << "  --log                 : enable logging" << std::endl;
    std::cout << std::endl;
}

int main(int argc, char *argv[]) {
    if (argc == 1) {
        print_help();
        return 0;
    }
    int arg = 0;
    auto get_next = [&]() {
        if (arg < argc-1) {
            return argv[++arg];
        } else {
            std::cout << "Error: Argument missing for " << argv[arg] << std::endl;
            exit(1);
        }
    };
    Config config;
    std::optional<std::string> input;
    auto show_version {true};
    try {
        while (++arg < argc) {
            if (boost::iequals(argv[arg], "--validate-sat")) {
                config.validate_sat = true;
            } else if (boost::iequals(argv[arg], "--validate-unsat")) {
                const auto bound {std::stoi(get_next())};
                if (bound >= 0) {
                    config.validate_unsat = bound;
                }
            } else if (boost::iequals(argv[arg], "--no-phasing")) {
                config.toggle_mode = false;
            } else if (boost::iequals(argv[arg], "--get-lemmas")) {
                config.get_lemmas = true;
            } else if (boost::iequals(argv[arg], "--log")) {
                config.log = true;
            } else if (boost::iequals(argv[arg], "--debug")) {
                config.debug = true;
            } else if (boost::iequals(argv[arg], "--stats")) {
                config.statistics = true;
            } else if (boost::iequals(argv[arg], "--version")) {
                version();
                return 0;
            } else if (boost::iequals(argv[arg], "--help")) {
                print_help();
                return 0;
            } else if (boost::iequals(argv[arg], "--no-version")) {
                show_version = false;
            } else if (boost::istarts_with(argv[arg], "--no-")) {
                auto found {false};
                for (const auto k: lemma_kind::values) {
                    if (boost::iequals(argv[arg], "--no-" + lemma_kind::str(k))) {
                        config.deactivate(k);
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    for (const auto k: preproc_kind::values) {
                        if (boost::iequals(argv[arg], "--no-" + preproc_kind::str(k))) {
                            config.deactivate(k);
                            found = true;
                            break;
                        }
                    }
                }
                if (!found) {
                    argument_parsing_failed(argv[arg]);
                }
            } else if (!input) {
                input = argv[arg];
            } else {
                argument_parsing_failed(argv[arg]);
            }
        }
        if (!input) {
            throw std::invalid_argument("missing input file");
        }
    } catch (const std::exception&) {
        print_help();
        throw;
    }
    z3::context ctx;
    Swine swine(config, ctx);
    Z3_func_decl const decls[]{swine.get_exp()};
    Z3_symbol const decl_names[]{swine.get_exp().name()};
    Z3_ast_vector v {Z3_parse_smtlib2_file(ctx, input->c_str(), 0, 0, 0, 1, decl_names, decls)};
    ctx.check_error();
    Z3_ast_vector_inc_ref(ctx, v);
    unsigned sz = Z3_ast_vector_size(ctx, v);
    for (unsigned i = 0; i < sz; ++i) {
        swine.add(z3::expr(ctx, Z3_ast_vector_get(ctx, v, i)));
    }
    Z3_ast_vector_dec_ref(ctx, v);
    const auto res {swine.check()};
    std::cout << res << std::endl;
    if (res == z3::sat) {
        std::cout << swine.get_model() << std::endl;
    }
    if (config.statistics) {
        std::cout << swine.get_stats() << std::endl;
    }
    if (show_version) {
        version();
    }
    return 0;
}
