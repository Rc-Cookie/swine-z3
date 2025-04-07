#pragma once

#include <string>
#include <optional>
#include <unordered_set>

namespace swine {

enum class PreprocKind {
    ConstantFolding, Rewriting, Inlining
};


namespace preproc_kind {

static constexpr size_t count = 3;
static const std::unordered_set<PreprocKind> values {PreprocKind::ConstantFolding, PreprocKind::Rewriting, PreprocKind::Inlining};

std::string str(const PreprocKind k);

}

std::ostream& operator<<(std::ostream &s, const PreprocKind kind);

}
