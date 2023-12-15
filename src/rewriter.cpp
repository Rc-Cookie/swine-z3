#include "rewriter.h"

namespace swine {

Rewriter::Rewriter(Util &util): util(util) {}

z3::expr Rewriter::rewrite(const z3::expr &t) {
    static const auto zero {util.ctx.int_val(0)};
    static const auto one {util.ctx.int_val(1)};
    static const auto mone {util.ctx.int_val(-1)};
    std::optional<z3::expr> res;
    if (t.num_args() == 0) {
        return t;
    } else {
        z3::expr_vector children{util.ctx};
        for (const auto &c: t.args()) {
            children.push_back(rewrite(c));
        }
        if (util.is_abstract_exp(t)) {
            const auto base {children[0]};
            const auto exp {children[1]};
            if (base.id() == one.id() || exp.id() == zero.id()) {
                res = util.term(1);
            } else if (exp.id() == one.id() || exp.id() == mone.id()) {
                res = base;
            } else if (util.is_value(exp)) {
                res = z3::pw(base, exp);
            } else if (util.is_abstract_exp(base)) {
                const auto inner_base {base.arg(0)};
                const auto inner_exp {base.arg(1)};
                res = util.make_exp(inner_base, exp * inner_exp);
            }
        } else if (t.decl().decl_kind() == Z3_OP_MUL) {
            std::unordered_map<unsigned, z3::expr_vector> exp_map;
            z3::expr_vector new_children{util.ctx};
            for (const auto &c: children) {
                if (util.is_abstract_exp(c)) {
                    const auto exp {c.arg(1)};
                    auto &set {exp_map.emplace(exp.id(), z3::expr_vector(util.ctx)).first->second};
                    set.push_back(c);
                } else {
                    new_children.push_back(c);
                }
            }
            bool changed {false};
            for (const auto &[_,set]: exp_map) {
                if (set.size() > 1) {
                    changed = true;
                    z3::expr_vector bases{util.ctx};
                    for (const auto &e: set) {
                        bases.push_back(e.arg(0));
                    }
                    new_children.push_back(util.make_exp(t.decl()(bases), set.back().arg(1)));
                } else {
                    new_children.push_back(*set.begin());
                }
            }
            if (changed) {
                res = t.decl()(new_children);
            }
        } else if (t.decl().decl_kind() == Z3_OP_POWER) {
            const auto fst {rewrite(t.arg(0))};
            const auto snd {rewrite(t.arg(1))};
            if (util.is_abstract_exp(fst) && util.is_value(snd) && util.value(snd) >= 0) {
                const auto base {fst.arg(0)};
                const auto exp {fst.arg(1)};
                res = util.make_exp(base, exp * snd);
            }
        }
        if (!res) {
            res = t.decl()(children);
        }
        return *res;
    }
}

}
