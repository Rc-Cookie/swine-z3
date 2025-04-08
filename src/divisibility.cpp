#include "divisibility.h"

namespace swine {

    using namespace z3;
    using namespace utils;

    Divisibility::Divisibility(const expr &divisibility) : Divisibility(parse(divisibility)) {
    }

    Divisibility::Divisibility(const Term &dividend, const cpp_int &divisor, const expr &original) : dividend(dividend), divisor(divisor), original(original) {
        assert(divisor > 0);
    }

    expr Divisibility::divisor_expr() const {
        return term(divisor, dividend);
    }

    expr Divisibility::to_expr() const {
        return dividend % divisor_expr() == 0;
    }

    bool Divisibility::is_const() const {
        return dividend.is_const();
    }

    Divisibility Divisibility::parse(const z3::expr &divisibility) {
        std::optional<Divisibility> d = try_parse(divisibility);
        assert(d);
        return *d;
    }

    std::optional<Divisibility> Divisibility::try_parse(const expr &divisibility) {

        if(!divisibility.is_eq())
            return {};

        const expr lhs = divisibility.arg(0);
        const expr rhs = divisibility.arg(1);

        bool modIsRhs = lhs.is_numeral();
        if(modIsRhs && rhs.is_numeral()) {
            if(lhs.id() == rhs.id())
                return {{ term(1, divisibility), 1, divisibility }};
            else return {{ term(1, divisibility), 2, divisibility }};
        }
        if(!modIsRhs && !rhs.is_numeral())
            return {};

        const expr &mod = modIsRhs ? rhs : lhs;
        const expr &zero = modIsRhs ? lhs : rhs;

        if(value(zero) != 0 || mod.decl().decl_kind() != Z3_OP_MOD)
            return {};

        const expr dividend = mod.arg(0);
        const expr divisor = mod.arg(1).simplify();

        if(!divisor.is_numeral())
            return {};

        const cpp_int divisorVal = value(divisor);
        if(divisorVal <= 0)
            return {};

        std::optional<Term> dividendTerm = Term::try_parse(dividend);
        if(!dividendTerm)
            return {};

        dividendTerm->constant = dividendTerm->constant % divisorVal;

        return {{ *dividendTerm, divisorVal, divisibility }};
    }

    std::vector<Divisibility> Divisibility::all_in(const expr &formula) {
        return find_values_in_bools<Divisibility>(formula, Divisibility::try_parse);
    }


    bool Divisibility::is_simple(const std::function<bool(const expr &)> &var_requirement) const {
        size_t varCount = dividend.variables.size();
        if(varCount != 1)
            return varCount == 0;
        const auto [coeff, var] = *dividend.var_sum().begin();
        return coeff == 1 && var_requirement(var);
    }

    bool Divisibility::is_in_power_comp() const {
        return is_simple(is_exp);
    }

    bool Divisibility::is_simple() const {
        return is_simple(is_var_or_func);
    }

    expr Divisibility::linearize() const {
        assert(is_in_power_comp());

        if(is_const())
            return original.ctx().bool_val(dividend.constant % divisor == 0);

        const expr exp = dividend.variables.begin()->second;
        const cpp_int base = value(exp.arg(0));

        cpp_int expS = 1;
        for(cpp_int s=0; s<divisor; s++) {
            if(expS % divisor + dividend.constant == 0) {
                cpp_int expT = 1;
                const expr var = exp.arg(1);
                for(cpp_int t=0; t<divisor; t++) {
                    if((dividend.constant * (expT - 1)) & divisor == 0)
                        return replace_ite(((abs(var) - term(s, exp)) % term(t, exp)) == 0);
                    expT = (t * base) & divisor;
                }
                return replace_ite(abs(var) == term(s, exp));
            }
            s = (s * base) % divisor;
        }
        return original.ctx().bool_val(false);
    }

    std::string Divisibility::to_string() const {
        std::ostringstream s;
        s << *this;
        return s.str();
    }

    const Term &Divisibility::get_dividend(const Divisibility &c) {
        return c.dividend;
    }

    const cpp_int &Divisibility::get_divisor(const Divisibility &c) {
        return c.divisor;
    }

    std::ostream& operator<<(std::ostream &s, const Divisibility &d) {
        return s << d.divisor << " | " << d.dividend;
    }
}
