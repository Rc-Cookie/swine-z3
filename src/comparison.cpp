#include "comparison.h"
#include "power_comp.h"

namespace swine {

    using namespace z3;

    Comparison::Comparison(const expr &comparison) : Comparison(parse(comparison)) {
    }

    Comparison::Comparison(const Term &term, Kind kind) : Comparison(term, kind, term.ctx) {
        original = normalized();
    }

    Comparison::Comparison(const Term &term, Kind kind, const expr &original) : term(term), kind(kind), original(original) {
    }

    expr Comparison::normalized() const {
        switch(kind) {
            case Kind::Equal:    return term.to_expr() == 0;
            case Kind::NotEqual: return term.to_expr() != 0;
            case Kind::Less:     return term.to_expr() < 0;
        }
        throw std::runtime_error("Unknown comparison kind");
    }

    std::string Comparison::to_string() const {
        std::ostringstream s;
        s << *this;
        return s.str();
    }

    std::ostream& operator<<(std::ostream &s, const Comparison::Kind &k) {
        switch(k) {
            case Comparison::Kind::Equal:    return s << "=";
            case Comparison::Kind::NotEqual: return s << "!=";
            case Comparison::Kind::Less:     return s << "<";
        }
        throw std::invalid_argument("Unknown comparison kind");
    }

    std::ostream& operator<<(std::ostream &s, const Comparison &c) {
        return s << c.term << " " << c.kind << " 0";
    }

    std::optional<Comparison> Comparison::try_parse(const expr &comparison) {
        if(!comparison.is_app())
            return { };

        switch(comparison.decl().decl_kind()) {
            case Z3_OP_LT: { // a < b <==> a - b < 0
                std::optional<Term> t = Term::try_parse(comparison.arg(0) - comparison.arg(1));
                if(t)
                    return Comparison(*t, Comparison::Kind::Less, comparison);
                else return { };
            }
            case Z3_OP_LE: { // a <= b <==> a - b <= 0 <==> a - b - 1 < 0
                std::optional<Term> t = Term::try_parse(comparison.arg(0) - comparison.arg(1) - 1);
                if(t)
                    return Comparison(*t, Comparison::Kind::Less, comparison);
                else return { };
            }
            case Z3_OP_GT: { // a > b <==> b < a <==> b - a < 0
                std::optional<Term> t = Term::try_parse(comparison.arg(1) - comparison.arg(0));
                if(t)
                    return Comparison(*t, Comparison::Kind::Less, comparison);
                else return { };
            }
            case Z3_OP_GE: { // a >= b <==> b <= a <==> b - a <= 0 <==> b - a - 1 < 0
                std::optional<Term> t = Term::try_parse(comparison.arg(1) - comparison.arg(0) - 1);
                if(t)
                    return Comparison(*t, Comparison::Kind::Less, comparison);
                else return { };
            }
            case Z3_OP_EQ: { // a = b <==> a - b = 0
                std::optional<Term> t = Term::try_parse(comparison.arg(0) - comparison.arg(1));
                if(t)
                    return Comparison(*t, Comparison::Kind::Equal, comparison);
                else return { };
            }
            case Z3_OP_DISTINCT: { // a != b <==> a - b != 0
                if(comparison.num_args() != 2)
                    return { };
                std::optional<Term> t = Term::try_parse(comparison.arg(0) - comparison.arg(1));
                if(t)
                    return Comparison(*t, Comparison::Kind::NotEqual, comparison);
                else return { };
            }
            case Z3_OP_NOT: {
                std::optional<Comparison> c = try_parse(comparison.arg(0));
                if(c) {
                    c->negate();
                    c->original = comparison;
                }
                return c;
            }
            default:
                return { };
        }
    }

    bool Comparison::is_in_power_comp() const {
        return (bool) PowerComp::try_parse(*this);
    }

    const bool Comparison::homogeneous_equals(const Comparison &c) const {
        return term.homogeneous_equals(c.term);
    }

    void Comparison::negate() {
        switch(kind) {
            case Kind::Equal: {
                kind = Kind::NotEqual;
                return;
            }
            case Kind::NotEqual: {
                kind = Kind::Equal;
                return;
            }
            case Kind::Less: {
                // !(x < 0) <==> x >= 0 <==> -x <= 0 <==> -x - 1 < 0
                term.negate();
                --term.constant;
                return;
            }
        }
        throw std::runtime_error("Unknown comparison kind");
    }

    const cpp_int Comparison::one_norm(const Comparison &c) {
        const cpp_int n = Term::one_norm(c.term);
        // 1-norm(t < 0) = 1-norm(t)
        // 1-norm(t != 0) = 1-norm(t < 0 || t > 0) = max(1-norm(t < 0), 1-norm(-t < 0)) = 1-norm(t < 0) = 1-norm(t)
        if(c.kind != Kind::Equal)
            return n;
        // 1-norm(t = 0) = 1-norm(t <= 0 || t >= 0) = max(1-norm(t <= 0), 1-norm(-t <= 0)) = max(1-norm(t - 1 < 0), 1-norm(-t - 1 < 0))
        return n + 1;
    }
}
