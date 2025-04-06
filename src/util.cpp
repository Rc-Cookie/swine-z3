#include "util.h"

namespace swine {

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

cpp_int Util::value(const z3::expr &term) const {
    return cpp_int(term.get_decimal_string(0));
}

z3::expr Util::term(const cpp_int &value) {
    return ctx.int_val(value.str().c_str());
}

bool Util::is_abstract_exp(const z3::expr &term) const {
    return term.num_args() == 2 && term.decl().name() == exp->name();
}

z3::expr Util::make_exp(const z3::expr &base, const z3::expr &exponent) {
    return (*exp)(base, exponent);
}

long long Util::to_int(const z3::expr &t) {
    try {
        return stoll(t.get_decimal_string(0));
    } catch (const std::out_of_range &e) {
        throw ExponentOverflow(t);
    }
}

bool Util::is_value(const z3::expr &t) const {
    return t.is_const() && t.decl().decl_kind() != Z3_OP_UNINTERPRETED;
}

}
