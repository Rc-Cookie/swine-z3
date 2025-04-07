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

    z3::expr preprocess(const z3::expr &term, bool advanced);

};

}
