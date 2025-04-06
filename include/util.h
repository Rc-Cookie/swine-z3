#pragma once

#include <z3++.h>
#include <boost/multiprecision/cpp_int.hpp>

#include "config.h"
#include "stats.h"

namespace swine {

using namespace boost::multiprecision;

class ExponentOverflow: public std::out_of_range {

    z3::expr t;

public:

    ExponentOverflow(const z3::expr &t);

    z3::expr get_t() const;

};

class Util {

public:

    const Config &config;
    const Statistics &stats;
    z3::context &ctx;
    std::unique_ptr<z3::func_decl> exp;

    Util(z3::context &ctx, const Config &config, const Statistics &stats);
    cpp_int value(const z3::expr &term) const;
    z3::expr term(const cpp_int &value);
    bool is_abstract_exp(const z3::expr &term) const;
    z3::expr make_exp(const z3::expr &base, const z3::expr &exponent);
    bool is_value(const z3::expr &t) const;

    static long long to_int(const z3::expr &t);

};

}
