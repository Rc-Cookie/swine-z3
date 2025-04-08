#pragma once

#include "lemma_kind.h"
#include "preproc_kind.h"

#include <unordered_set>

// msg not inside parentheses on purpose, so that you can write stuff like 'log("Var: " << v)'
#define _log(config, msg) do { if((config).log || (config).debug) { std::cout << msg << std::endl; } } while(0)
#define _debug(config, msg) do { if((config).debug) { std::cout << msg << std::endl; } } while(0)

namespace swine {

class Config {

private:

    std::unordered_set<LemmaKind> active_lemma_kinds {lemma_kind::values};
    std::unordered_set<PreprocKind> active_preprocessings{preproc_kind::values};

public:

    bool validate_sat {false};
    std::optional<unsigned int> validate_unsat {};
    bool log {false};
    bool statistics {false};
    bool get_lemmas {false};
    bool model {false};
    bool non_lazy {false};
    bool debug {false};
    unsigned rlimit {0};
    bool toggle_mode {true};

    void deactivate(const LemmaKind k);

    bool is_active(const LemmaKind k) const;

    void deactivate(const PreprocKind k);

    bool is_active(const PreprocKind k) const;

    void set_rlimit(unsigned rlimit);

};

}
