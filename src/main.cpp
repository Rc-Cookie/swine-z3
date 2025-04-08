#include "swine.h"
#include "version.h"
#include "lemma_kind.h"
#include "preproc_kind.h"
#include "config.h"

#include <boost/algorithm/string.hpp>
#include <z3++.h>
#include <filesystem>
#include <fstream>

using namespace swine;
namespace fs = std::filesystem;

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
    std::cout << "  --model               : force an algorithm that produces a model if SAT" << std::endl;
    std::cout << "  --non-lazy            : use non-lazy variant of EIA_n solver (if applicable)" << std::endl;
    std::cout << "  --stats               : print statistics in the end" << std::endl;
    std::cout << "  --help                : print this text and exit" << std::endl;
    std::cout << "  --version             : print the SwInE version and exit" << std::endl;
    std::cout << "  --no-version          : omit the SwInE version at the end of the output" << std::endl;
    std::cout << "  --log                 : enable logging" << std::endl;
    std::cout << std::endl;
}

std::pair<z3::check_result, Statistics> run_file(Config &config, std::string file, std::string name, bool single) {
    // Print file name first so that it is clear what's currently calculating. When not logging anything in between,
    // sat/unsat/unknown will be printed in the same line, so no std::endl.
    if(config.log || config.debug)
        std::cout << name << std::endl;
    else std::cout << name << std::string(name.length() < 80 ? 80 - name.length() : 0, ' ') << std::flush;

    Timer timer;

    // Load file
    z3::context ctx;
    Swine swine(config, ctx);
    Z3_func_decl const decls[]{swine.get_exp()};
    Z3_symbol const decl_names[]{swine.get_exp().name()};
    Z3_ast_vector v {Z3_parse_smtlib2_file(ctx, file.c_str(), 0, 0, 0, 1, decl_names, decls)};
    ctx.check_error();
    Z3_ast_vector_inc_ref(ctx, v);

    unsigned sz = Z3_ast_vector_size(ctx, v);
    for (unsigned i = 0; i < sz; ++i) {
        swine.add(z3::expr(ctx, Z3_ast_vector_get(ctx, v, i)));
    }
    Z3_ast_vector_dec_ref(ctx, v);

    // Actually solve
    const auto res {swine.check()};

    // Print result and duration
    Timer::duration duration = timer;
    if(config.log || config.debug)
        std::cout << std::string(80, ' ');
    std::cout << ": " << (res == z3::sat ? "sat    " : res == z3::unsat ? "unsat  " : "unknown") << " in " << std::chrono::duration_cast<std::chrono::milliseconds>(duration).count() << " ms" << std::endl;

    // Don't print model if not explicitly requested, we're not logging, and are solving many files at once
    if(res == z3::sat && swine.has_model() && (single || config.model || config.log || config.debug))
        std::cout << swine.get_model() << std::endl;
    // Same for statistics, will be summarized instead after all are done
    if(config.statistics && (single || config.log || config.debug))
        std::cout << swine.get_stats() << std::endl;

    return { res, swine.get_stats() };
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
            } else if (boost::iequals(argv[arg], "--model")) {
                config.model = true;
            } else if (boost::iequals(argv[arg], "--non-lazy")) {
                config.non_lazy = true;
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

    Timer::duration totalDuration = Timer::duration::zero();

    // If directory, run all files recursively, otherwise just run the file itself
    if(fs::is_directory(*input)) {
        unsigned int i = 0;
        std::vector<std::tuple<std::string, z3::check_result, Timer::duration>> results;
        for(const auto &e : fs::recursive_directory_iterator(*input)) {
            if(!e.is_regular_file())
                continue;

            ++i;
            std::string file = fs::relative(e).string();
            if(e.path().filename().string().starts_with('.'))
                continue;
            std::string name = fs::relative(e, *input).string();

            Timer timer;
            const auto [res, stats] = run_file(config, file, name, false);
            Timer::duration duration = timer;
            totalDuration += duration;
            results.push_back({ name, res, duration });
        }

        // If we have a bunch of output, summarize in compact form
        if(config.log || config.debug) {
            std::cout << "\n-------- Summary --------" << std::endl;
            for(const auto &[n,r,ms] : results)
                std::cout << n << std::string(n.length() < 80 ? 80 - n.length() : 0, ' ') << ": " << (r == z3::sat ? "sat    " : r == z3::unsat ? "unsat  " : "unknown") << " in " << std::chrono::duration_cast<std::chrono::milliseconds>(ms).count() << " ms" << std::endl;
        }
    }
    else if(fs::is_regular_file(*input)) {
        Timer timer;
        const auto [_, stats] = run_file(config, *input, fs::path(*input).filename().string(), true);
        totalDuration += timer;
    }
    else throw z3::exception("File not found / not a file or a directory");

    if(config.statistics || config.log || config.debug)
        std::cout << "\nTotal time: " << std::chrono::duration_cast<std::chrono::milliseconds>(totalDuration).count() << " ms" << std::endl;

    if (show_version) {
        version();
    }
    return 0;
}
