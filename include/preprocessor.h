#pragma once

#include "rewriter.h"
#include "constant_propagator.h"

namespace swine {

struct PreprocResult {
    z3::expr simple;
    z3::expr full;
    std::optional<cpp_int> eia_n_base;
};

class Preprocessor {

    Util &util;
    Rewriter rewriter;
    ConstantPropagator constant_propagator;

public:

    Preprocessor(Util &util);

    PreprocResult preprocess(const z3::expr &term, bool full);

};

}
