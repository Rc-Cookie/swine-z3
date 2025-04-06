#include "exp_finder.h"

namespace swine {

ExpGroup::ExpGroup(const z3::expr &t, Util &util):
    t(t),
    util(util),
    ground_base(utils::is_value(t.arg(0))),
    neg_base(ground_base && utils::value(t.arg(0)) < 0) {}

z3::expr_vector ExpGroup::all() const {
    z3::expr_vector res{util.ctx};
    const auto base {t.arg(0)};
    const auto exp {t.arg(1)};
    res.push_back(t);
    res.push_back(util.make_exp(base, -exp));
    if (neg_base || !ground_base) {
        res.push_back(util.make_exp(-base, exp));
        res.push_back(util.make_exp(-base, -exp));
    }
    return res;
}

z3::expr_vector ExpGroup::maybe_non_neg_base() const {
    if (!neg_base) {
        return all();
    }
    z3::expr_vector res{util.ctx};
    const auto base {t.arg(0)};
    const auto exp {t.arg(1)};
    res.push_back(util.make_exp(-base, exp));
    res.push_back(util.make_exp(-base, -exp));
    return res;
}

bool ExpGroup::has_ground_base() const {
    return ground_base;
}

z3::expr ExpGroup::orig() const {
    return t;
}

ExpFinder::ExpFinder(Util &util): util(util) {}

void ExpFinder::find_exps(const z3::expr &term, z3::expr_vector &res) {
    if (term.num_args() > 0) {
        for (auto c: term.args()) {
            find_exps(c, res);
        }
        if (utils::is_exp(term)) {
            res.push_back(term);
        }
    }
}

std::vector<ExpGroup> ExpFinder::find_exps(const z3::expr &term) {
    z3::expr_vector res{util.ctx};
    find_exps(term, res);
    std::vector<ExpGroup> groups;
    for (const auto &t: res) {
        groups.emplace_back(t, util);
    }
    return groups;
}

}
