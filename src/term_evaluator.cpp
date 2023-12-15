#include "term_evaluator.h"

#include <boost/algorithm/string.hpp>

namespace swine {

TermEvaluator::TermEvaluator(Util &util): util(util) {}

z3::expr TermEvaluator::evaluate(const z3::expr &expression, const z3::model &model) {
    if (expression.num_args() == 0) {
        return model.eval(expression, true);
    } else if (util.is_abstract_exp(expression)) {
        const auto fst {util.value(evaluate(expression.arg(0), model))};
        const auto snd {util.to_int(evaluate(expression.arg(1), model))};
        return util.term(pow(fst, abs(snd)));
    } else {
        z3::expr_vector children{util.ctx};
        for (const auto &c: expression.args()) {
            children.push_back(evaluate(c, model));
        }
        return expression.decl()(children);
    }
}

}
