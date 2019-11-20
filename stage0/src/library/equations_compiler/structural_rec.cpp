/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/class.h"
#include "library/util.h"
#include "library/suffixes.h"
#include "library/pattern_attribute.h"
#include "library/app_builder.h"
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/structural_rec.h"
#include "library/equations_compiler/elim_match.h"
#include "frontends/lean/elaborator.h"

namespace lean {
#define trace_struct(Code) lean_trace(name({"eqn_compiler", "structural_rec"}), type_context_old ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)
#define trace_struct_aux(Code) lean_trace(name({"eqn_compiler", "structural_rec"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); Code)
#define trace_debug_struct(Code) lean_trace(name({"debug", "eqn_compiler", "structural_rec"}), type_context_old ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)
#define trace_debug_struct_aux(Code) lean_trace(name({"debug", "eqn_compiler", "structural_rec"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); Code)

struct structural_rec_fn {
    environment      m_env;
    elaborator &     m_elab;
    metavar_context  m_mctx;
    local_context    m_lctx;

    expr             m_ref;
    equations_header m_header;
    expr             m_fn_type;
    unsigned         m_arity;
    unsigned         m_arg_pos;
    bool             m_reflexive;
    bool             m_use_ibelow;
    buffer<unsigned> m_indices_pos;
    expr             m_motive_type;

    structural_rec_fn(environment const & env, elaborator & elab,
                      metavar_context const & mctx, local_context const & lctx):
        m_env(env), m_elab(elab), m_mctx(mctx), m_lctx(lctx) {
    }

    [[ noreturn ]] void throw_error(char const * msg) {
        throw generic_exception(m_ref, msg);
    }

    [[ noreturn ]] void throw_error(sstream const & strm) {
        throw generic_exception(m_ref, strm);
    }

    type_context_old mk_type_context() {
        return type_context_old(m_env, m_mctx, m_lctx, m_elab.get_cache(), transparency_mode::Semireducible);
    }

    environment const & env() const { return m_env; }
    metavar_context const & mctx() const { return m_mctx; }

    /** \brief Auxiliary object for checking whether recursive application are
        structurally smaller or not */
    struct check_rhs_fn {
        type_context_old & m_ctx;
        expr           m_lhs;
        expr           m_fn;
        expr           m_pattern;
        unsigned       m_arg_idx;

        check_rhs_fn(type_context_old & ctx, expr const & lhs, expr const & fn, expr const & pattern, unsigned arg_idx):
            m_ctx(ctx), m_lhs(lhs), m_fn(fn), m_pattern(pattern), m_arg_idx(arg_idx) {}

        bool is_constructor(expr const & e) const {
            return is_constant(e) && ::lean::is_constructor(m_ctx.env(), const_name(e));
        }

        expr whnf(expr const & e) {
            /* We only unfold patterns and reducible/instance definitions */
            return m_ctx.whnf_transparency_pred(e, [&](name const & n) {
                    return
                        has_pattern_attribute(m_ctx.env(), n) ||
                        is_instance(m_ctx.env(), n) ||
                        is_reducible(m_ctx.env(), n);
                });
        }

        /** \brief Return true iff \c s is structurally smaller than \c t OR equal to \c t */
        bool is_le(expr const & s, expr const & t) {
            return m_ctx.is_def_eq(s, t) || is_lt(s, t);
        }

        /** Return true iff \c s is structurally smaller than \c t */
        bool is_lt(expr s, expr t) {
            s = whnf(s);
            t = whnf(t);
            if (is_app(s)) {
                expr const & s_fn = get_app_fn(s);
                if (!is_constructor(s_fn))
                    return is_lt(s_fn, t); // f < t ==> s := f a_1 ... a_n < t
            }
            buffer<expr> t_args;
            expr const & t_fn = get_app_args(t, t_args);
            if (!is_constructor(t_fn))
                return false;
            return std::any_of(t_args.begin(), t_args.end(),
                               [&](expr const & t_arg) { return is_le(s, t_arg); });
        }

        /** \brief Return true iff all recursive applications in \c e are structurally smaller than \c m_pattern. */
        bool check_rhs(expr const & e) {
            switch (e.kind()) {
            case expr_kind::BVar:  case expr_kind::MVar:
            case expr_kind::FVar:  case expr_kind::Const:
            case expr_kind::Sort:  case expr_kind::Lit:
            case expr_kind::Local:
                return true;
            case expr_kind::App: {
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                if (!check_rhs(fn))
                    return false;
                for (unsigned i = 0; i < args.size(); i++)
                    if (!check_rhs(args[i]))
                        return false;
                if (is_fvar(fn) && fvar_name(fn) == fvar_name(m_fn)) {
                    /* recusive application */
                    if (m_arg_idx < args.size()) {
                        expr const & arg = args[m_arg_idx];
                        /* arg must be structurally smaller than m_pattern */
                        if (!is_lt(arg, m_pattern)) {
                            name fname = *m_ctx.get_local_pp_name(m_fn);
                            trace_struct_aux(tout() << "structural recursion on argument #" << (m_arg_idx+1)
                                             << " was not used "
                                             << "for '" << fname << "'\nargument #" << (m_arg_idx+1)
                                             << " in the application\n  "
                                             << e << "\nis not structurally smaller than the one occurring in "
                                             << "the equation left-hand-side\n  "
                                             << m_lhs << "\n";);
                            return false;
                        }
                    } else {
                        /* function is not fully applied */
                        name fname = *m_ctx.get_local_pp_name(m_fn);
                        trace_struct_aux(tout() << "structural recursion on argument #" << (m_arg_idx+1) << " was not used "
                                         << "for '" << fname << "' because of the partial application\n  "
                                         << e << "\n";);
                        return false;
                    }
                }
                return true;
            }
            case expr_kind::MData:
                return check_rhs(mdata_expr(e));
            case expr_kind::Proj:
                return check_rhs(proj_expr(e));
            case expr_kind::Let:
                if (!check_rhs(let_value(e))) {
                    return false;
                } else {
                    type_context_old::tmp_locals locals(m_ctx);
                    return check_rhs(instantiate(let_body(e), locals.push_local_from_let(e)));
                }
            case expr_kind::Lambda:
            case expr_kind::Pi:
                if (!check_rhs(binding_domain(e))) {
                    return false;
                } else {
                    type_context_old::tmp_locals locals(m_ctx);
                    return check_rhs(instantiate(binding_body(e), locals.push_local_from_binding(e)));
                }
            }
            lean_unreachable();
        }

        bool operator()(expr const & e) {
            return check_rhs(e);
        }
    };

    bool check_rhs(type_context_old & ctx, expr const & lhs, expr const & fn, expr pattern, unsigned arg_idx, expr const & rhs) {
        pattern = ctx.whnf(pattern);
        return check_rhs_fn(ctx, lhs, fn, pattern, arg_idx)(rhs);
    }

    bool check_eq(type_context_old & ctx, expr const & eqn, unsigned arg_idx) {
        unpack_eqn ue(ctx, eqn);
        buffer<expr> args;
        expr const & fn  = get_app_args(ue.lhs(), args);
        return check_rhs(ctx, ue.lhs(), fn, args[arg_idx], arg_idx, ue.rhs());
    }

    static bool depends_on_locals(expr const & e, type_context_old::tmp_locals const & locals) {
        return depends_on_any(e, locals.as_buffer().size(), locals.as_buffer().data());
    }

    /* Return true iff argument arg_idx is a candidate for structural recursion.
       If the argument type is an indexed family, we store the position of the
       indices (in the function being defined) at m_indices_pos.
       This method also updates m_reflexive (true iff the inductive datatype is reflexive). */
    bool check_arg_type(type_context_old & ctx, unpack_eqns const & ues, unsigned arg_idx) {
        m_indices_pos.clear();
        type_context_old::tmp_locals locals(ctx);
        /* We can only use structural recursion on arg_idx IF
           1- Type is an inductive datatype with support for the brec_on construction.
           2- Type parameters do not depend on other arguments of the function being defined. */
        expr fn      = ues.get_fn(0);
        expr fn_type = ctx.infer(fn);
        for (unsigned i = 0; i < arg_idx; i++) {
            fn_type = ctx.whnf(fn_type);
            if (!is_pi(fn_type)) throw_ill_formed_eqns();
            fn_type = instantiate(binding_body(fn_type), locals.push_local_from_binding(fn_type));
        }
        fn_type = ctx.try_to_pi(fn_type);
        if (!is_pi(fn_type)) throw_ill_formed_eqns();
        expr arg_type = ctx.relaxed_whnf(binding_domain(fn_type));
        buffer<expr> I_args;
        expr I        = get_app_args(arg_type, I_args);
        name fname    = *ctx.get_local_pp_name(fn);
        if (!is_constant(I) || !is_inductive(m_env, const_name(I))) {
            trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                         << "for '" << fname << "' because type is not inductive\n  "
                         << arg_type << "\n";);
            return false;
        }
        name I_name   = const_name(I);
        inductive_val I_val = m_env.get(I_name).to_inductive_val();
        m_reflexive   = I_val.is_reflexive();
        if (!m_env.find(name(I_name, g_brec_on))) {
            trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                         << "for '" << fname << "' because the inductive type '" << I << "' does have brec_on recursor\n  "
                         << arg_type << "\n";);
            return false;
        }
        if (m_reflexive && !m_env.find(name(I_name, "binduction_on"))) {
            trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                         << "for '" << fname << "' because the reflexive inductive type '" << I << "' does "
                         << "have binduction_on recursor\n  "
                         << arg_type << "\n";);
            return false;
        }
        unsigned nindices = I_val.get_nindices();
        if (nindices > 0) {
            lean_assert(I_args.size() >= nindices);
            unsigned first_index_pos = I_args.size() - nindices;
            for (unsigned i = first_index_pos; i < I_args.size(); i++) {
                expr const & idx = I_args[i];
                if (!is_fvar(idx)) {
                    trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                                 << "for '" << fname << "' because the inductive type '" << I << "' is an indexed family, "
                                 << "and index #" << (i+1) << " is not a variable\n  "
                                 << arg_type << "\n";);
                    return false;
                }
                /* Index must be an argument of the function being defined */
                unsigned idx_pos = 0;
                buffer<expr> const & xs = locals.as_buffer();
                for (; idx_pos < xs.size(); idx_pos++) {
                    expr const & x = xs[idx_pos];
                    if (fvar_name(x) == fvar_name(idx)) {
                        break;
                    }
                }
                if (idx_pos == xs.size()) {
                    trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                                 << "for '" << fname << "' because the inductive type '" << I << "' is an indexed family, "
                                 << "and index #" << (i+1) << " is not an argument of the function being defined\n  "
                                 << arg_type << "\n";);
                    return false;
                }
                /* Index can only depend on other indices in the function being defined. */
                expr idx_type = ctx.infer(idx);
                for (unsigned j = 0; j < idx_pos; j++) {
                    bool j_is_not_index =
                        std::find(m_indices_pos.begin(), m_indices_pos.end(), j) == m_indices_pos.end();
                    if (j_is_not_index && depends_on(idx_type, xs[j])) {
                        trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                                     << "for '" << fname << "' because the inductive type '" << I << "' is an indexed family, "
                                     << "and index #" << (i+1) << " depends on argument #" << (j+1) << " of '" << fn << "' "
                                     << "which is not an index of the inductive datatype\n  "
                                     << arg_type << "\n";);
                        return false;
                    }
                }
                m_indices_pos.push_back(idx_pos);
                /* Each index can only occur once */
                for (unsigned j = first_index_pos; j < i; j++) {
                    expr const & prev_idx = I_args[j];
                    if (fvar_name(prev_idx) == fvar_name(idx)) {
                        trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                                     << "for '" << fname << "' because the inductive type '" << I << "' is an indexed family, "
                                     << "and index #" << (i+1) << " and #" << (j+1) << " must be different variables\n  "
                                     << arg_type << "\n";);
                        return false;
                    }
                }
            }
        }
        for (unsigned i = 0; i < I_args.size() - nindices; i++) {
            if (depends_on_locals(I_args[i], locals)) {
                trace_struct(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                             << "for '" << fname << "' because type parameter depends on previous arguments\n  "
                             << arg_type << "\n";);
                return false;
            }
        }
        return true;
    }

    /* Return true iff structural recursion can be performed on one of the arguments.
       If the result is true, then m_arg_pos will contain the position of the argument,
       and m_indices_pos the position of its indices (when the type of the
       argument is an indexed family). */
    bool find_rec_arg(type_context_old & ctx, unpack_eqns const & ues) {
        buffer<expr> const & eqns = ues.get_eqns_of(0);
        unsigned arity = ues.get_arity_of(0);
        for (unsigned i = 0; i < arity; i++) {
            if (check_arg_type(ctx, ues, i)) {
                bool ok = true;
                for (expr const & eqn : eqns) {
                    if (!check_eq(ctx, eqn, i)) {
                        ok = false;
                        break;
                    }
                }
                if (ok) {
                    m_arg_pos = i;
                    return true;
                }
            }
        }
        return false;
    }

    /* Return the type of the new function.
       It also sets the m_motive_type field. */
    expr mk_new_fn_motive_types(type_context_old & ctx, unpack_eqns const & ues) {
        type_context_old::tmp_locals locals(ctx);
        expr fn        = ues.get_fn(0);
        expr fn_type   = ctx.infer(fn);
        unsigned arity = ues.get_arity_of(0);
        expr rec_arg;
        buffer<expr> args;
        buffer<expr> other_args;
        for (unsigned i = 0; i < arity; i++) {
            fn_type = ctx.whnf(fn_type);
            if (!is_pi(fn_type)) throw_ill_formed_eqns();
            expr arg = locals.push_local_from_binding(fn_type);
            args.push_back(arg);
            if (i == m_arg_pos) {
                rec_arg = arg;
            } else if (std::find(m_indices_pos.begin(), m_indices_pos.end(), i) == m_indices_pos.end()) {
                other_args.push_back(arg);
            }
            fn_type  = instantiate(binding_body(fn_type), arg);
        }
        buffer<expr> idx_args;
        for (unsigned i : m_indices_pos)
            idx_args.push_back(args[i]);
        buffer<expr> I_params;
        expr I = get_app_args(ctx.relaxed_whnf(ctx.infer(rec_arg)), I_params);
        unsigned nindices = m_indices_pos.size();
        I_params.shrink(I_params.size() - nindices);
        expr  motive = ctx.mk_pi(other_args, fn_type);
        level u      = get_level(ctx, motive);
        m_use_ibelow = m_reflexive && is_zero(u);
        if (m_reflexive) {
            if (!is_zero(u) && !is_not_zero(u))
                throw_error(sstream() << "invalid equations, "
                            << "when trying to recurse over reflexive inductive datatype "
                            << "'" << const_name(I) << "' "
                            << "(argument #" << (m_arg_pos+1) << ") "
                            << "the universe level of the resultant universe must be zero OR "
                            << "not zero for every level assignment "
                            << "(possible solutions: provide universe levels explicitly, "
                            << "or force well_founded recursion by using `using_well_founded` keyword)");
            if (!is_zero(u)) {
                // For reflexive type, the type of brec_on and ibelow perform a +1 on the motive universe.
                // Example: for a reflexive formula type, we have:
                //     formula.below.{l_1} : Π {C : formula → Type.{l_1+1}}, formula → Type.{max (l_1+1) 1}
                if (auto dlvl = dec_level(u)) {
                    u = *dlvl;
                } else {
                    throw_error(sstream() << "invalid equations, "
                                << "when trying to recurse over reflexive inductive datatype "
                                << "'" << const_name(I) << "' "
                                << "(argument #" << (m_arg_pos+1) << ") "
                                << "the universe level of the resultant universe must be zero OR "
                                << "not zero for every level assignment. "
                                << "The compiler managed to establish that the resultant "
                                << "universe level u := (" << u << ") is never zero, but failed to compute "
                                << "the new resulting level (u - 1) "
                                << "(possible solutions: provide universe levels explicitly, "
                                << "or force well_founded recursion by using `using_well_founded` keyword)");
                }
            }
        }
        motive          = ctx.mk_lambda(idx_args, ctx.mk_lambda(rec_arg, motive));
        lean_assert(is_constant(I));
        buffer<level> below_lvls;
        if (!m_use_ibelow)
            below_lvls.push_back(u);
        for (level const & v : const_levels(I))
            below_lvls.push_back(v);
        name below_name = name(const_name(I), m_use_ibelow ? "ibelow" : "below");
        expr below      = mk_app(mk_constant(below_name, levels(below_lvls)), I_params);
        m_motive_type   = binding_domain(ctx.relaxed_whnf(ctx.infer(below)));
        below           = mk_app(mk_app(mk_app(below, motive), idx_args), rec_arg);
        locals.push_local("_F", below);
        return locals.mk_pi(fn_type);
    }

    struct elim_rec_apps_failed {};

    struct elim_rec_apps_fn : public replace_visitor_with_tc {
        expr                     m_fn;
        unsigned                 m_arg_pos;
        buffer<unsigned> const & m_indices_pos;
        expr                     m_F;
        expr                     m_C;

        elim_rec_apps_fn(type_context_old & ctx, expr const & fn,
                         unsigned arg_pos, buffer<unsigned> const & indices_pos, expr const & F, expr const & C):
            replace_visitor_with_tc(ctx),
            m_fn(fn), m_arg_pos(arg_pos), m_indices_pos(indices_pos), m_F(F), m_C(C) {}

        /** \brief Retrieve result for \c a from the below dictionary \c d. \c d is a term made of products,
            and m_C (the abstract local). */
        optional<expr> to_below(expr const & d, expr const & a, expr const & F) {
            expr const & fn = get_app_fn(d);
            trace_struct_aux(tout() << "d: " << d << ", a: " << a << ", F: " << F << "\n";);
            if (is_constant(fn, get_pprod_name()) || is_constant(fn, get_and_name())) {
                bool prop   = is_constant(fn, get_and_name());
                expr d_arg1 = m_ctx.whnf(app_arg(app_fn(d)));
                expr d_arg2 = m_ctx.whnf(app_arg(d));
                if (auto r = to_below(d_arg1, a, mk_pprod_fst(m_ctx, F, prop)))
                    return r;
                else if (auto r = to_below(d_arg2, a, mk_pprod_snd(m_ctx, F, prop)))
                    return r;
                else
                    return none_expr();
            } else if (is_fvar(fn)) {
                if (fvar_name(m_C) == fvar_name(fn) && m_ctx.is_def_eq(app_arg(d), a))
                    return some_expr(F);
                return none_expr();
            } else if (is_pi(d)) {
                if (is_app(a)) {
                    expr new_d = m_ctx.whnf(instantiate(binding_body(d), app_arg(a)));
                    return to_below(new_d, a, mk_app(F, app_arg(a)));
                } else {
                    return none_expr();
                }
            } else {
                return none_expr();
            }
        }

        bool is_index_pos(unsigned idx) const {
            return std::find(m_indices_pos.begin(), m_indices_pos.end(), idx) != m_indices_pos.end();
        }

        expr elim(expr const & e, buffer<expr> const & args) {
            /* Replace motives with abstract one m_C.
               We use the abstract motive m_C as "marker". */
            buffer<expr> below_args;
            expr const & below_cnst = get_app_args(m_ctx.infer(m_F), below_args);
            unsigned nindices = m_indices_pos.size();
            below_args[below_args.size() - 1 - 1 /* major */ - nindices] = m_C;
            expr abst_below   = mk_app(below_cnst, below_args);
            expr below_dict   = m_ctx.whnf(abst_below);
            expr rec_arg      = m_ctx.whnf(args[m_arg_pos]);
            if (optional<expr> b = to_below(below_dict, rec_arg, m_F)) {
                expr r = *b;
                for (unsigned i = 0; i < args.size(); i++) {
                    if (i != m_arg_pos && !is_index_pos(i))
                        r = mk_app(r, args[i]);
                }
                return r;
            } else {
                trace_struct_aux(tout() << "failed to eliminate recursive application using 'below'\n" <<
                                 e << "\n";);
                throw elim_rec_apps_failed();
            }
        }

        virtual expr visit_fvar(expr const & e) {
            if (fvar_name(e) == fvar_name(m_fn)) {
                /* unexpected occurrence of recursive function */
                trace_struct_aux(tout() << "unexpected occurrence of recursive function: " << e << "\n";);
                throw elim_rec_apps_failed();
            }
            return e;
        }

        virtual expr visit_app(expr const & e) {
            expr const & fn = get_app_fn(e);
            if (is_fvar(fn) && fvar_name(fn) == fvar_name(m_fn)) {
                buffer<expr> args;
                get_app_args(e, args);
                if (m_arg_pos >= args.size()) throw elim_rec_apps_failed();
                buffer<expr> new_args;
                for (expr const & arg : args)
                    new_args.push_back(visit(arg));
                return elim(e, new_args);
            } else {
                return replace_visitor_with_tc::visit_app(e);
            }
        }
    };

    /* Return true if we need to complete equations by expanding the recursive argument.

       For example, suppose we have, where the recursive argument is the second

       def f : nat → nat → nat
       | (x+1) (y+1) := f (x+10) y
       | _     _     := 1

       this function returns true because
       1) We need to perform case analysis in the first argument (first equation),
          (flag has_case_analysis_before in the followin procedure); and
       2) W have an equation (second) where the recursive argument is a variable
          (flag incomplete).
    */
    bool must_complete_rec_arg(type_context_old & ctx, unpack_eqns const & ues) {
        if (m_arg_pos == 0) return false;
        buffer<expr> const & eqns = ues.get_eqns_of(0);
        bool has_case_analysis_before = false;
        bool incomplete = false;
        for (expr const & eqn : eqns) {
            unpack_eqn ue(ctx, eqn);
            buffer<expr> lhs_args;
            get_app_args(ue.lhs(), lhs_args);

            if (!has_case_analysis_before) {
                for (unsigned i = 0; i < m_arg_pos; i++) {
                    if (!is_fvar(lhs_args[i]) && !is_inaccessible(lhs_args[i])) {
                        has_case_analysis_before = true;
                        break;
                    }
                }
            }

            if (is_fvar(lhs_args[m_arg_pos]))
                incomplete = true;

            if (has_case_analysis_before && incomplete)
                return true;
        }
        return false;
    }

    void update_eqs(type_context_old & ctx, unpack_eqns & ues, expr const & fn, expr const & new_fn) {
        /* C is a temporary "abstract" motive, we use it to access the "g_brec_on dictionary".
           The g_brec_on dictionary is an element of type below, and it is the last argument of the new function. */
        type_context_old::tmp_locals locals(ctx);
        expr C = locals.push_local("_C", m_motive_type);
        buffer<expr> & eqns = ues.get_eqns_of(0);
        buffer<expr> new_eqns;
        bool complete = must_complete_rec_arg(ctx, ues);
        for (expr const & eqn : eqns) {
            unpack_eqn ue(ctx, eqn);
            expr lhs = ue.lhs();
            expr rhs = ue.rhs();
            buffer<expr> lhs_args;
            get_app_args(lhs, lhs_args);
            if (complete && is_fvar(lhs_args[m_arg_pos])) {
                expr var = lhs_args[m_arg_pos];
                for_each_compatible_constructor(ctx, var,
                [&](expr const & c, buffer<expr> const & new_c_vars) {
                   buffer<expr> new_vars;
                   buffer<expr> from;
                   buffer<expr> to;
                   update_telescope(ctx, ue.get_vars(), var, c, new_c_vars,
                                    new_vars, from, to);
                   buffer<expr> new_lhs_args(lhs_args);
                   new_lhs_args[m_arg_pos] = c;
                   for (unsigned i = m_arg_pos + 1; i < new_lhs_args.size(); i++)
                       new_lhs_args[i] = replace_locals(new_lhs_args[i], from, to);
                   expr new_lhs = mk_app(new_fn, new_lhs_args);
                   expr type    = ctx.whnf(ctx.infer(new_lhs));
                   lean_assert(is_pi(type));
                   type_context_old::tmp_locals extra(ctx);
                   expr F       = extra.push_local(binding_name(type), binding_domain(type));
                   new_vars.push_back(F);
                   new_lhs      = mk_app(new_lhs, F);
                   /* The lhs was a variable, so we don't need to update the rhs using elim_rec_apps_fn.
                      Reason: the rhs should not contain recursive equations.
                      But, we need to update the locals. */
                   expr new_rhs = replace_locals(ue.rhs(), from, to);
                   expr new_eqn = copy_pos(ue.get_nested_src(),
                                           mk_equation(new_lhs, new_rhs, ue.ignore_if_unused()));
                   new_eqns.push_back(copy_pos(eqn, ctx.mk_lambda(new_vars, new_eqn)));
                });
            } else {
                expr new_lhs = mk_app(new_fn, lhs_args);
                expr type    = ctx.whnf(ctx.infer(new_lhs));
                lean_assert(is_pi(type));
                expr F       = ue.add_var(binding_name(type), binding_domain(type));
                new_lhs      = mk_app(new_lhs, F);
                ue.lhs()     = new_lhs;
                ue.rhs()     = elim_rec_apps_fn(ctx, fn, m_arg_pos, m_indices_pos, F, C)(rhs);
                new_eqns.push_back(ue.repack());
            }
        }
        eqns = new_eqns;
    }

    optional<expr> elim_recursion(expr const & e) {
        type_context_old ctx = mk_type_context();
        unpack_eqns ues(ctx, e);
        if (ues.get_num_fns() != 1) {
            trace_struct(tout() << "structural recursion is not supported for mutually recursive functions:";
                         for (unsigned i = 0; i < ues.get_num_fns(); i++)
                             tout() << " " << ues.get_fn(i);
                         tout() << "\n";);
            return none_expr();
        }
        m_fn_type = ctx.infer(ues.get_fn(0));
        m_arity   = ues.get_arity_of(0);
        expr fn = ues.get_fn(0);
        lean_assert(ctx.lctx().find_local_decl(fn));
        if (!find_rec_arg(ctx, ues)) return none_expr();
        lean_assert(ctx.lctx().find_local_decl(fn));
        name fname = *ctx.get_local_pp_name(fn);
        trace_struct(tout() << "using structural recursion on argument #" << (m_arg_pos+1) <<
                     " for '" << fname << "'\n";);
        expr new_fn_type = mk_new_fn_motive_types(ctx, ues);
        trace_struct(
            tout() << "\n";
            tout() << "new function type: " << new_fn_type << "\n";
            tout() << "motive type:       " << m_motive_type << "\n";);
        expr new_fn = ues.update_fn_type(0, new_fn_type);
        try {
            update_eqs(ctx, ues, fn, new_fn);
        } catch (elim_rec_apps_failed &) {
            trace_struct(tout() << "failed to compile equations/match using structural recursion, "
                         << "when creating new set of equations\n";);
            return none_expr();
        }
        expr new_eqns = ues.repack();
        lean_trace("eqn_compiler", tout() << "using structural recursion:\n" << new_eqns << "\n";);
        m_mctx = ctx.mctx();
        return some_expr(new_eqns);
    }

    expr whnf_upto_below(type_context_old & ctx, name const & I_name, expr const & below_type) {
        name below_name(I_name, "below");
        name ibelow_name(I_name, "ibelow");
        return ctx.whnf_head_pred(below_type, [&](expr const & e) {
                expr const & fn = get_app_fn(e);
                return !is_constant(fn) || (const_name(fn) != below_name && const_name(fn) != ibelow_name);
            });
    }

    bool is_index_pos(unsigned idx) const {
        return std::find(m_indices_pos.begin(), m_indices_pos.end(), idx) != m_indices_pos.end();
    }

    expr mk_function(expr const & aux_fn) {
        type_context_old ctx = mk_type_context();
        type_context_old::tmp_locals locals(ctx);
        buffer<expr> fn_args;
        expr aux_fn_type = ctx.infer(aux_fn);
        for (unsigned i = 0; i < m_arity + 1 /* below argument */; i++) {
            aux_fn_type = ctx.relaxed_whnf(aux_fn_type);
            lean_assert(is_pi(aux_fn_type));
            expr arg = locals.push_local_from_binding(aux_fn_type);
            if (i < m_arity) fn_args.push_back(arg);
            aux_fn_type = instantiate(binding_body(aux_fn_type), arg);
        }
        buffer<expr> const & aux_fn_args = locals.as_buffer();
        unsigned nindices = m_indices_pos.size();
        expr rec_arg      = aux_fn_args[m_arg_pos];
        expr rec_arg_type = ctx.relaxed_whnf(ctx.infer(rec_arg));
        buffer<expr> I_args;
        expr const & I    = get_app_args(rec_arg_type, I_args);
        name I_name       = const_name(I);
        unsigned nparams  = I_args.size() - nindices;
        expr below_arg    = aux_fn_args.back();
        expr below_type   = whnf_upto_below(ctx, I_name, ctx.infer(below_arg));
        buffer<expr> below_args;
        expr below        = get_app_args(below_type, below_args);
        expr motive       = below_args[nparams];
        name brec_on_name = name(I_name, m_use_ibelow ? g_binduction_on : g_brec_on);
        expr brec_on_fn   = mk_constant(brec_on_name, const_levels(below));
        buffer<expr> brec_on_args;
        buffer<expr> F_domain; /* domain for F argument for brec_on */
        brec_on_args.append(nparams, I_args.data());
        brec_on_args.push_back(motive);
        for (unsigned idx_pos : m_indices_pos) {
            brec_on_args.push_back(aux_fn_args[idx_pos]);
            F_domain.push_back(aux_fn_args[idx_pos]);
        }
        brec_on_args.push_back(rec_arg);
        F_domain.push_back(rec_arg);
        F_domain.push_back(below_arg);
        buffer<expr> extra_args;
        for (unsigned i = 0; i < fn_args.size(); i++) {
            if (i != m_arg_pos && !is_index_pos(i)) {
                F_domain.push_back(aux_fn_args[i]);
                extra_args.push_back(aux_fn_args[i]);
            }
        }
        expr F = ctx.mk_lambda(F_domain, mk_app(aux_fn, aux_fn_args));
        brec_on_args.push_back(F);
        expr new_fn = ctx.mk_lambda(fn_args, mk_app(mk_app(brec_on_fn, brec_on_args), extra_args));
        lean_trace("eqn_compiler", tout() << "result:\n" << new_fn << "\ntype:\n" << ctx.infer(new_fn) << "\n";);
        if (m_header.m_is_unsafe) {
            /* We don't create auxiliary definitions for meta-definitions because we don't create lemmas
               for them. */
            return new_fn;
        } else {
            expr r;
            std::tie(m_env, r) = mk_aux_definition(m_env, m_elab.get_options(), m_mctx, m_lctx, m_header,
                                                   head(m_header.m_fn_names),
                                                   head(m_header.m_fn_actual_names),
                                                   m_fn_type, new_fn);
            return r;
        }
    }

    optional<eqn_compiler_result> operator()(expr const & eqns) {
        m_ref    = eqns;
        m_header = get_equations_header(eqns);
        auto new_eqns = elim_recursion(eqns);
        if (!new_eqns) return {};
        elim_match_result R = elim_match(m_env, m_elab, m_mctx, m_lctx, *new_eqns);
        expr fn = mk_function(R.m_fn);
        list<expr> counter_examples = map2<expr>(R.m_counter_examples, [&] (list<expr> const & es_) {
            buffer<expr> es; to_buffer(es_, es);
            return mk_app(fn, es.size()-1, es.data());
        });
        return optional<eqn_compiler_result>({ {fn}, counter_examples });
    }
};

optional<eqn_compiler_result> try_structural_rec(environment & env, elaborator & elab, metavar_context & mctx,
                                                 local_context const & lctx, expr const & eqns) {
    structural_rec_fn F(env, elab, mctx, lctx);
    if (auto r = F(eqns)) {
        env  = F.env();
        mctx = F.mctx();
        return r;
    } else {
        return {};
    }
}

void initialize_structural_rec() {
    register_trace_class({"eqn_compiler", "structural_rec"});
    register_trace_class({"debug", "eqn_compiler", "structural_rec"});
}
void finalize_structural_rec() {}
}