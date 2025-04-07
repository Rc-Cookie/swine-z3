#include "term.h"

namespace swine {

    using namespace std::views;
    using namespace range_utils;
    using namespace z3;



    Term::Term(const expr &term) : ctx(term) {
        if(!populate(term))
            throw exception("Invalid term");
    }

    Term Term::zero() const {
        return zero(ctx);
    }

    Term Term::zero(const expr &ctx) {
        return Term(ctx, true);
    }

    expr Term::homogeneous() const {
        return variables
                | values
                | transform([&](const expr &v){
                    const cpp_int coeff = coefficients.at(v.id());
                    return coeff == 1 ? v : utils::term(coeff, v) * v;
                })
                | sum(utils::term(0, ctx));
    }

    void Term::negate() {
        for(std::pair<const unsigned int, cpp_int> &entry : coefficients)
            entry.second = -entry.second;
        constant = -constant;
    }

    void Term::add(const cpp_int &coeff, const expr &var) {
        if(coeff == 0)
            return;
        unsigned int id = var.id();
        if(variables.add(var))
            coefficients.emplace(id, coeff);
        else {
            const cpp_int ownCoeff = coefficients.at(id);
            if(coeff != -ownCoeff)
                coefficients.emplace(id, ownCoeff + coeff).first->second = ownCoeff + coeff;
            else {
                variables.erase(var);
                coefficients.erase(id);
            }
        }
    }

    void Term::add(const Term &t) {
        for(const auto &[id,v] : t.variables)
            add(t.coefficients.at(id), v);
        constant += t.constant;
    }

    void Term::subtract(const Term &t) {
        for(const auto &[id,v] : t.variables)
            add(-t.coefficients.at(id), v);
        constant -= t.constant;
    }

    void Term::multiply(const Term &t, Term &res) const {

        res.set_zero();

        for(const auto &[coeff,v] : var_sum()) {
            for(const auto &[oCoeff, ov] : t.var_sum())
                res.add(coeff * oCoeff, v * ov);
            res.add(coeff * t.constant, v);
        }
        for(const auto &[oCoeff, ov] : t.var_sum())
            res.add(constant * oCoeff, ov);
        res.constant = constant * t.constant;
    }



    bool Term::populate(const expr &term) {

        set_zero();

        if(term.is_numeral()) {
            constant = utils::value(term);
            return true;
        }
        if(utils::is_var_or_func(term)) {
            add(1, term);
            return true;
        }

        const auto kind = term.is_app() ? term.decl().decl_kind() : Z3_OP_INTERNAL;
        switch(kind) {
            case Z3_OP_UMINUS: {
                if(!populate(term.arg(0)))
                    return false;
                negate();
                return true;
            }
            case Z3_OP_ADD:
            case Z3_OP_SUB: {
                if(!populate(term.arg(0)))
                    return false;
                Term rhs = zero();
                for(unsigned int i=1; i<term.num_args(); i++) {
                    if(!rhs.populate(term.arg(i)))
                        return false;
                    if(kind == Z3_OP_ADD)
                        add(rhs);
                    else subtract(rhs);
                }
                return true;
            }
            case Z3_OP_MUL: {
                Term lhs = zero(), rhs = zero();
                if(term.num_args() == 2) {
                    if(!lhs.populate(term.arg(0)) || !rhs.populate(term.arg(1)))
                        return false;
                    lhs.multiply(rhs, *this);
                }
                else {
                    if(!populate(term.arg(0)))
                        return false;
                    for(unsigned int i=1; i<term.num_args(); i++) {
                        if(!rhs.populate(term.arg(i)))
                            return false;
                        lhs = *this;
                        lhs.multiply(rhs, *this);
                    }
                }
                return true;
            }
            default: {
                return false;
            }
        }
    }

    std::string Term::to_string() const  {
        std::ostringstream s;
        s << *this;
        return s.str();
    }

    std::ostream& write_var(std::ostream &s, const z3::expr &v) {
        if(utils::is_exp(v))
            return write_var(write_var(s << "exp(", v.arg(0)) << ", ", v.arg(1)) << ")";
        return s << v;
    }

    std::ostream& operator<<(std::ostream &s, const Term &t) {
        if(t.is_const())
            return s << t.constant;
        if(t.is_homogeneous() && t.variables.size() == 1 && t.coefficients.begin()->second == 1)
            return write_var(s, t.variables.begin()->second);
        s << "(";
        bool first = true;
        for(auto [coeff,v] : t.var_sum()) {
            if(first)
                first = false;
            else if(coeff > 0)
                s << " + ";
            else {
                s << " - ";
                coeff = -coeff;
            }

            if(coeff == 1)
                write_var(s,v);
            else if(coeff == -1)
                write_var(s << "-", v);
            else write_var(s << coeff << " * ", v);
        }
        if(t.constant > 0)
            s << " + " << t.constant;
        else if(t.constant < 0)
            s << " - " << -t.constant;
        return s << ")";
    }
}
