#include "constant_propagator.h"

namespace swine {

ConstantPropagator::ConstantPropagator(Util &util): util(util) {}

z3::expr ConstantPropagator::propagate(const z3::expr &expression) const {
    const auto zero {util.ctx.int_val(0)};
    const auto one {util.ctx.int_val(1)};
    if (expression.num_args() == 0) {
        return expression;
    } else {
        z3::expr_vector children{util.ctx};
        bool ground {true};
        for (const auto &c: expression.args()) {
            children.push_back(propagate(c));
            ground &= utils::is_value(children.back());
        }
        if (expression.decl().decl_kind() == Z3_OP_POWER) {
            if (children.size() != 2) {
                throw std::invalid_argument("Pow must have exactly two arguments.");
            }
            if (ground) {
                return util.term(pow(utils::value(children[0]), utils::to_int(children[1])));
            } else if (children[0].id() == one.id() || children[1].id() == zero.id()) {
                return one;
            } else if (children[1].id() == one.id()) {
                return children[0];
            }
        } else if (ground && utils::is_exp(expression)) {
            return util.term(pow(utils::value(children[0]), abs(utils::to_int(children[1]))));
        }
        const auto res {expression.decl()(children)};
        if (ground) {
            return res.simplify();
        } else {
            return res;
        }
    }
}

}
