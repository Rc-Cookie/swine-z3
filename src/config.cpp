#include "config.h"
#include <iostream>

#define log(msg) _log(*this, msg)

namespace swine {

void Config::deactivate(const LemmaKind k) {
    log("Deactivating lemma kind " << k);
    active_lemma_kinds.erase(k);
}

bool Config::is_active(const LemmaKind k) const {
    return active_lemma_kinds.contains(k);
}

void Config::deactivate(const PreprocKind k) {
    log("Deactivating preprocessor kind " << k);
    active_preprocessings.erase(k);
}

bool Config::is_active(const PreprocKind k) const {
    return active_preprocessings.contains(k);
}

void Config::deactivate(const Algorithm a) {
    log("Deactivating algorithm " << a);
    active_algorithms.erase(a);
}

void Config::force(const swine::Algorithm a) {
    log("Deactivating all algorithms except " << a);
    active_algorithms.clear();
    active_algorithms.emplace(a);
}

bool Config::is_active(const Algorithm a) const {
    return active_algorithms.contains(a);
}

const std::unordered_set<Algorithm> &Config::get_algorithms() const {
    return active_algorithms;
}

void Config::set_rlimit(unsigned rlimit) {
    log("Setting rLimit of " << rlimit);
    this->rlimit = rlimit;
}

}
