#include "power_comp.h"
#include "divisibility.h"
#include <boost/math/constants/constants.hpp>
#include <ranges>

namespace swine {

    using namespace z3;
    using namespace std::views;
    using namespace range_utils;
    using namespace utils;

    PowerComp::PowerComp(const cpp_int &base, const cpp_int &a, const expr &x, const cpp_int &b, Kind kind):
        base(base), a(a), b(b), x(x), y({}), kind(kind) {
        if((kind == Kind::Equal || kind == Kind::NotEqual) && b < 0) {
            this->a = -a;
            this->b = -b;
        }
    }

    PowerComp::PowerComp(const cpp_int &base, const cpp_int &a, const expr &x, const cpp_int &b, const expr &y, Kind kind):
        base(base), a(a), b(b), x(x), y(y), kind(kind) {
        if(kind == Kind::Equal || kind == Kind::NotEqual) {
            if(b < 0) {
                this->a = -a;
                this->b = -b;
            }
            // b >= 0
            if(this->a > this->b) {
                swap(this->a, this->b);
                this->x = y;
                this->y = x;
            }
        }
    }

    expr PowerComp::a_expr() const {
        return term(a, x);
    };

    expr PowerComp::b_expr() const {
        return term(b, x);
    }

    expr PowerComp::as_expr(const Util &util) const {
        const expr lhs = util.term(a) * util.make_exp(x);
        const expr rhs = y ? util.term(b) * util.make_exp(*y) : util.term(b);

        switch(kind) {
            case Kind::Equal:       return lhs == rhs;
            case Kind::NotEqual:    return !(lhs == rhs);
            case Kind::Less:        return lhs < rhs;
            case Kind::LessOrEqual: return lhs <= rhs;
        }
        throw std::runtime_error("Unknown power comp type");
    }

    Comparison PowerComp::as_comparison(const swine::Util &util) const {
        Term term = Term::zero(x);
        term.add(a, util.make_exp(x));
        if(y)
            term.add(-b, util.make_exp(*y));
        else term.constant = -b;

        expr original = as_expr(util);

        switch(kind) {
            case Kind::Equal:    return Comparison(term, Comparison::Kind::Equal, original);
            case Kind::NotEqual: return Comparison(term, Comparison::Kind::NotEqual, original);
            case Kind::Less:     return Comparison(term, Comparison::Kind::Less, original);
            case Kind::LessOrEqual: {
                --term.constant;
                return Comparison(term, Comparison::Kind::Less, original);
            }
        }
        throw std::runtime_error("Unknown power comp type");
    }

    bool PowerComp::is_clearly_const() const {
        return a == 0 || a.sign() != b.sign();
    }

    bool PowerComp::is_const() const {
        if(is_clearly_const())
            return true;
        if(kind != Kind::Equal && kind != Kind::NotEqual)
            return false;
        cpp_int ba,r;
        divide_qr(b, a, ba, r);
        return r == 0 && log_exact(base, ba);
    }

    z3::expr PowerComp::linearize() const {
        if(is_clearly_const()) {
            switch(kind) {
                case Kind::Equal:       return x.ctx().bool_val(a == 0 && b == 0);
                case Kind::NotEqual:    return x.ctx().bool_val(a.sign() != b.sign());
                case Kind::Less:        return x.ctx().bool_val(a < 0 || b > 0);
                case Kind::LessOrEqual: return x.ctx().bool_val(a <= 0 || b >= 0);
            }
            throw std::runtime_error("Unknown power comp type");
        }
        switch(kind) {
            case Kind::Equal: return linearize_equal();
            case Kind::NotEqual: return !linearize_equal();
            case Kind::Less: return linearize_less();
            case Kind::LessOrEqual: return linearize_less() || linearize_equal();
        }
        throw std::runtime_error("Unknown power comp type");
    }

    expr PowerComp::linearize_equal() const {
        // a * 2^x == b * 2^y <==> 2^x == 2^y * b/a <==> |x| == |y| + log(b/a)

        // No floor(log) or ceil(log) - log(b/a) must evaluate to an integer
        // If b/a is already no integer, neither will log(b/a) be
        cpp_int ba, r;
        divide_qr(b, a, ba, r); // ba = b/a, r = b%a
        if(r != 0)
            return x.ctx().bool_val(false);

        std::optional<cpp_int> log = log_exact(base, ba);
        if(!log)
            return x.ctx().bool_val(false);

        if(!y) {
            // y = 0 ==> |x| == log(b/a)
            if(*log)
                // log >= 0 -> (x >= 0 && x = log) || (x < 0 && x = -log) <==> x = log || x = -log
                return (x == term(*log, x)) || (x == term(-*log, x));
            else return x == 0;
        }
        else {
            // |x| = |y| + log(b/a)
            if(*log) {
                expr logExpr = term(*log, x);
                return (x >= 0 && ((*y >= 0 &&  x ==  *y + logExpr)
                                || (*y  < 0 &&  x == -*y + logExpr)))
                    || (x < 0  && ((*y >= 0 && -x ==  *y + logExpr)
                                || (*y  < 0 && -x == -*y + logExpr)));
            }
            else return (x == *y) || (x == -*y);
        }
    }

    expr PowerComp::linearize_less() const {
        cpp_int log;
        if(a > 0) { // ==> b > 0
            // ceil(log(b/a)) = ceil(log(ceil(b/a)))
            log = ceil_log(base, (b + a - 1) / a);
        }
        else { // ==> a < 0 && b < 0
            // floor(log(b/a)) = floor(log(floor(b/a)))
            log = floor_log(base, b / a);
        }

        if(!y) { // <==> y = 0
            if(a > 0) {
                // |x| < ceil(log(b/a))
                if(log)
                    return x < term(log, x) && x > term(-log, x);
                else return x.ctx().bool_val(false);
            }
            else {
                // |x| > floor(log(b/a))
                if(log)
                    return x > term(log, x) || x < term(-log, x);
                else return x != 0;
            }
        }
        else {
            expr logExpr = term(log, x);
            if(a > 0) {
                // |x| < |y| + ceil(log(b/a))
                return (x >= 0 && ((*y >= 0 && x < *y + logExpr) || (*y < 0 && x < -*y + logExpr))) || (x < 0 && ((*y >= 0 && -x < *y + logExpr) || (*y < 0 && -x < -*y + logExpr)));
            }
            else {
                // |x| > |y| + floor(log(b/a))
                return (x >= 0 && ((*y >= 0 && x > *y + logExpr) || (*y < 0 && x > -*y + logExpr))) || (x < 0 && ((*y >= 0 && -x > *y + logExpr) || (*y < 0 && -x > -*y + logExpr)));
            }
        }
    }

    std::string PowerComp::to_string() const {
        std::ostringstream s;
        s << *this;
        return s.str();
    }

    std::ostream& operator<<(std::ostream &s, const PowerComp::Kind &kind) {
        switch(kind) {
            case PowerComp::Kind::Equal:       return s << "=";
            case PowerComp::Kind::NotEqual:    return s << "!=";
            case PowerComp::Kind::Less:        return s << "<";
            case PowerComp::Kind::LessOrEqual: return s << "<=";
        }
        throw std::invalid_argument("Unknown power comp kind");
    }

    std::ostream& operator<<(std::ostream &s, const PowerComp &comp) {
        s << comp.a << " * exp(" << comp.x << ") " << comp.kind << " " << comp.b;
        if(comp.y)
            s << " * exp(" << *comp.y << ")";
        return s;
    }

    std::optional<PowerComp> PowerComp::try_parse(const expr &comparison) {
        std::optional<Comparison> c = Comparison::try_parse(comparison);
        if(c)
            return try_parse(*c);
        return { };
    }

    std::optional<PowerComp> PowerComp::try_parse(const Comparison &comparison) {
        size_t varCount = comparison.term.variables.size();
        if(varCount == 1) {
            const auto &[coeff, exp] = *comparison.term.var_sum().begin();
            if(!is_exp(exp))
                return { };
            cpp_int base = value(exp.arg(0));
            switch(comparison.kind) {
                case Comparison::Kind::Equal:    return PowerComp(base, coeff, exp.arg(1), -comparison.term.constant, Kind::Equal);
                case Comparison::Kind::NotEqual: return PowerComp(base, coeff, exp.arg(1), -comparison.term.constant, Kind::NotEqual);
                case Comparison::Kind::Less:     return PowerComp(base, coeff, exp.arg(1), -comparison.term.constant, Kind::Less);
            }
        }
        if(varCount != 2 || (comparison.term.constant != 0 && (comparison.kind != Comparison::Kind::Less || comparison.term.constant != -1)))
            return { };

        const auto var_sum = comparison.term.var_sum() | to_pairs<cpp_int, expr>();
        const auto &[a,ex] = var_sum.at(0);
        const auto &[b,ey] = var_sum.at(1);

        if(!is_exp(ex) || !is_exp(ey))
            return { };

        cpp_int base1 = value(ex.arg(0));
        cpp_int base2 = value(ey.arg(0));
        if(base1 != base2)
            return { };

        switch(comparison.kind) {
            case Comparison::Kind::Equal:    return PowerComp(base1, a, ex.arg(1), -b, ey.arg(1), Kind::Equal);
            case Comparison::Kind::NotEqual: return PowerComp(base1, a, ex.arg(1), -b, ey.arg(1), Kind::NotEqual);
            case Comparison::Kind::Less:     return PowerComp(base1, a, ex.arg(1), -b, ey.arg(1), comparison.term.constant == 0 ? Kind::Less : Kind::LessOrEqual);
        }
        throw std::runtime_error("Unknown power comp type");
    }


    /**
     * Collects power comparisons, divisibility constraints in PowerComp and all exp() expressions
     * that are not part of the former, that occur in the given expression.
     *
     * @param expr The expression in which to search
     * @param out_exps Set to insert exp calls into which are not in the extended PowerComp fragment
     * @param out_original_power_comp_exprs Set of the original expressions from which the PowerComp
     *                                      objects were parsed
     * @param out_power_comps Map to insert power comparisons into, mapped by the id of the expression
     *                        that they originated from
     * @param out_power_comp_divs List to insert divisibility constraints inside the PowerComp fragment
     *                            into
     */
    void collect_exps_outside_power_comp(const z3::expr &expr, expr_set &out_exps, expr_set &out_original_power_comp_exprs, std::unordered_map<unsigned int, PowerComp> &out_power_comps, std::vector<Divisibility> &out_power_comp_divs) {
        if(!expr.is_bool() || !expr.is_app()) {
            collect_vars(expr, out_exps, false, true);
            return;
        }
        if(expr.is_const())
            return;

        switch(expr.decl().decl_kind()) {
            case Z3_OP_NOT:
            case Z3_OP_AND:
            case Z3_OP_OR:
            case Z3_OP_IMPLIES:
            case Z3_OP_XOR: {
                for(unsigned int i=0; i<expr.num_args(); ++i)
                    collect_exps_outside_power_comp(expr.arg(i), out_exps, out_original_power_comp_exprs, out_power_comps, out_power_comp_divs);
                return;
            }
            case Z3_OP_EQ: {
                std::optional<Divisibility> d = Divisibility::try_parse(expr);
                if(d && d->is_in_power_comp()) {
                    out_power_comp_divs.push_back(*d);
                    return;
                }
                /* continue */
            }
            case Z3_OP_DISTINCT:
            case Z3_OP_LT:
            case Z3_OP_GT:
            case Z3_OP_LE:
            case Z3_OP_GE: {
                std::optional<PowerComp> pc = PowerComp::try_parse(expr);
                if(pc) {
                    out_original_power_comp_exprs.add(expr);
                    out_power_comps.emplace(expr.id(), *pc);
                }
                else collect_vars(expr, out_exps, false, true);
                return;
            }
            default: {
            }
        }
    }


    z3::expr linearize(const z3::expr &expr, const std::vector<z3::expr> &variables) {

        expr_set not_in_power_comp;
        expr_set original_exprs;
        std::unordered_map<unsigned int, PowerComp> power_comps;
        std::vector<Divisibility> power_comp_divs;
        collect_exps_outside_power_comp(expr, not_in_power_comp, original_exprs, power_comps, power_comp_divs);

        not_in_power_comp = not_in_power_comp
                | values
                | filter(is_exp)
                | transform([](const z3::expr &exp){ return exp.arg(1); })
                | to<expr_set>();

        z3::expr result = expr;
        std::unordered_set<unsigned int> replaced;

        bool any = false;

        for(const z3::expr var : variables) {
            if(not_in_power_comp.contains(var.id()))
                continue;

            unsigned int id = var.id();
            any = true;
            std::vector<std::pair<z3::expr, z3::expr>> replacements;

            for(const auto &[orig, pc] : power_comps) {
                if(replaced.contains(orig) || (pc.x.id() != id && (!pc.y || pc.y->id() != id)))
                    continue;
                replacements.push_back({ original_exprs.at(orig), pc.linearize() });
                replaced.emplace(orig);
            }

            for(const Divisibility &d : power_comp_divs) {
                if(replaced.contains(d.original.id()) || d.dividend.variables.begin()->second.arg(1).id() != id)
                    continue;
                replacements.push_back({ d.original, d.linearize() });
                replaced.emplace(d.original.id());
            }

            result = substitute_all(result, replacements);
        }

        if(!any) {
            // Not strictly against the contract of the function, but rarely intended. Use
            // Ansi color codes to color red and bold, don't use stderr since that may not be
            // properly synced with stdout, making it hard to see where the error occurred.
            std::cout << "\x1b[1;31mLinearize() did not find anything to linearize with variables " << variables << " in " << expr << "\x1b[0m" << std::endl;
        }

        return result;
    }
}
