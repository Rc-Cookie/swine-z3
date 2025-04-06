#include "util.h"

namespace swine {


namespace utils {

    cpp_int value(const z3::expr &term) {
        return cpp_int(term.get_decimal_string(0));
    }

    cpp_int value(const z3::expr &term, const z3::model &interpretation) {
        return value(interpretation.eval(term, true));
    }

    long long to_int(const z3::expr &t) {
        try {
            return stoll(t.get_decimal_string(0));
        } catch (const std::out_of_range &e) {
            throw ExponentOverflow(t);
        }
    }

    bool is_value(const z3::expr &t) {
        return t.is_const() && t.decl().decl_kind() != Z3_OP_UNINTERPRETED;
    }

    bool is_uninterpreted(const z3::expr &expr, bool vars, bool functions) {
        if(!expr.is_app() || expr.decl().decl_kind() != Z3_OP_UNINTERPRETED)
            return false;
        return expr.num_args() == 0 ? vars : functions;
    }

    bool is_var(const z3::expr &expr) {
        return is_uninterpreted(expr, true, false);
    }

    bool is_var_or_func(const z3::expr &expr) {
        return is_uninterpreted(expr, true, true);
    }

    bool is_func(const z3::expr &expr) {
        return is_uninterpreted(expr, false, true);
    }

    bool is_exp(const z3::expr &e) {
        return is_func(e) && e.num_args() == 2 && e.decl().name().str() == "exp";
    }

    z3::expr term(const cpp_int &value, const z3::expr &ctx) {
        return ctx.ctx().int_val(value.str().c_str());
    }
}



ExponentOverflow::ExponentOverflow(const z3::expr &t): std::out_of_range(""), t(t) {}

Util::Util(z3::context &ctx, const Config &config, Statistics &stats):
    config(config),
    stats(stats),
    ctx(ctx) {
    z3::sort_vector domain {ctx};
    domain.push_back(ctx.int_sort());
    domain.push_back(ctx.int_sort());
    exp = std::make_unique<z3::func_decl>(ctx.function("exp", domain, ctx.int_sort()));
}

z3::expr ExponentOverflow::get_t() const {
    return t;
}

z3::expr Util::term(const cpp_int &value) {
    return ctx.int_val(value.str().c_str());
}

z3::expr Util::make_exp(const z3::expr &base, const z3::expr &exponent) {
    return (*exp)(base, exponent);
}

}
