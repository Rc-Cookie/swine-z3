#pragma once

#include "rewriter.h"
#include "constant_propagator.h"

namespace swine {

class Preprocessor {

    Util &util;
    Rewriter rewriter;
    ConstantPropagator constant_propagator;

public:

    Preprocessor(Util &util);

    std::pair<z3::expr, std::optional<cpp_int>> preprocess(const z3::expr &term, bool full);

};

}
