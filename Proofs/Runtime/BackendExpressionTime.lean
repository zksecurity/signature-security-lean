import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendDataSize

/-! # Structural time bounds for compiled expressions

One lemma per expression constructor: the compiled constructor's time is the subterms' times plus
a few structural fees, each paid at a frame width `W` bounding every represented value in sight.
Subterm times and value sizes are hypotheses, so a bound for a concrete expression is assembled
bottom-up without unfolding the whole compiled term at once. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.Expression

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) → Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

local notation "bound" e => compileBound rep data P primitive laws dataLaws primitiveBound e

/-- The structural fee at frame `W`. -/
def frameFee (overhead : Nat → Nat) (W : Nat) : Nat := overhead (16 * W)

include sizes

omit mono in
/-- A variable's value is no larger than its environment. -/
theorem var_size {Γ a} (v : Var Γ a) (env : Env base Γ) :
    Q.size (rep.ty a) (v.get env) ≤ Q.size (rep.env Γ) env := by
  induction v with
  | @here a Γ => exact sizes.fst_le (rep.ty a) (rep.env Γ) env
  | @there a b Γ v ih => exact (ih env.2).trans (sizes.snd_le (rep.ty b) (rep.env Γ) env)

include mono

theorem var_time {Γ a} (v : Var Γ a) (env : Env base Γ) (W : Nat) (henv : Q.size (rep.env Γ) env ≤ W) :
    (bound (.var v : Expr Op Γ a)).time env ≤ (2 * v.depth + 1) * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  induction v generalizing W with
  | @here a Γ =>
    have h := sizes.fst_le (rep.ty a) (rep.env Γ) env
    dsimp only [compileBound, variableBound, LocalBound.fst, Var.depth, LanguageRepresentation.env] at *
    grind only
  | @there a b Γ v ih =>
    have hs := sizes.snd_le (rep.ty b) (rep.env Γ) env
    have hv := var_size rep sizes v env.2
    have hrec := ih env.2 W ((sizes.snd_le (rep.ty b) (rep.env Γ) env).trans henv) hfee
    dsimp only [compileBound, variableBound, LocalBound.compose, LocalBound.snd, Var.depth, Var.get,
      LanguageRepresentation.env] at *
    have h1 := hfee (Q.size (StepClass.HasProd.prod (rep.ty b) (rep.env Γ)) env + Q.size (rep.env Γ) env.2) (by omega)
    have h2 := hfee (Q.size (StepClass.HasProd.prod (rep.ty b) (rep.env Γ)) env + Q.size (rep.env Γ) env.2 +
      Q.size (rep.ty a) (v.get env.2)) (by omega)
    have hsplit : (2 * (v.depth + 1) + 1) * frameFee overhead W =
      (2 * v.depth + 1) * frameFee overhead W + 2 * frameFee overhead W := by ring
    omega

theorem unit_time {Γ} (env : Env base Γ) (W : Nat) (henv : Q.size (rep.env Γ) env ≤ W)
    (hu : Q.size rep.data.unit () ≤ W) :
    (bound (.unit : Expr Op Γ .unit)).time env ≤ frameFee overhead W := by
  dsimp only [compileBound, DataCostLaws.unitBound, frameFee]
  exact mono (by omega)

theorem bool_time {Γ} (b : Bool) (env : Env base Γ) (W : Nat) (henv : Q.size (rep.env Γ) env ≤ W)
    (hu : Q.size rep.data.unit () ≤ W) (hb : Q.size rep.data.bool b ≤ W) :
    (bound (.bool b : Expr Op Γ .bool)).time env ≤ 3 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  dsimp only [compileBound, LocalBound.compose, DataCostLaws.unitBound, DataCostLaws.boolBound] at *
  grind only

theorem nat_time {Γ} (n : Nat) (env : Env base Γ) (W : Nat) (henv : Q.size (rep.env Γ) env ≤ W)
    (hu : Q.size rep.data.unit () ≤ W) (hn : Q.size rep.data.nat n ≤ W) :
    (bound (.nat n : Expr Op Γ .nat)).time env ≤ 3 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  dsimp only [compileBound, LocalBound.compose, DataCostLaws.unitBound, DataCostLaws.natBound] at *
  grind only

theorem pair_time {Γ a b} (l : Expr Op Γ a) (r : Expr Op Γ b) (env : Env base Γ) (W Tl Tr : Nat)
    (hh : header ≤ W) (henv : Q.size (rep.env Γ) env ≤ W)
    (hl : Q.size (rep.ty a) (l.denote P env) ≤ W) (hr : Q.size (rep.ty b) (r.denote P env) ≤ W)
    (tl : (bound l).time env ≤ Tl) (tr : (bound r).time env ≤ Tr) :
    (bound (.pair l r)).time env ≤ Tl + Tr + frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hp := sizes.prod_le (rep.ty a) (rep.ty b) (l.denote P env, r.denote P env)
  dsimp only [compileBound, LocalBound.pair] at *
  grind only

theorem fst_time {Γ a b} (p : Expr Op Γ (.pair a b)) (env : Env base Γ) (W Tp : Nat)
    (henv : Q.size (rep.env Γ) env ≤ W) (hp : Q.size (rep.ty (.pair a b)) (p.denote P env) ≤ W)
    (tp : (bound p).time env ≤ Tp) :
    (bound (.fst p)).time env ≤ Tp + 2 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hf := sizes.fst_le (rep.ty a) (rep.ty b) (p.denote P env)
  dsimp only [compileBound, LocalBound.compose, LocalBound.fst, LanguageRepresentation.ty] at *
  grind only

theorem snd_time {Γ a b} (p : Expr Op Γ (.pair a b)) (env : Env base Γ) (W Tp : Nat)
    (henv : Q.size (rep.env Γ) env ≤ W) (hp : Q.size (rep.ty (.pair a b)) (p.denote P env) ≤ W)
    (tp : (bound p).time env ≤ Tp) :
    (bound (.snd p)).time env ≤ Tp + 2 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hf := sizes.snd_le (rep.ty a) (rep.ty b) (p.denote P env)
  dsimp only [compileBound, LocalBound.compose, LocalBound.snd, LanguageRepresentation.ty] at *
  grind only

include lists in
theorem nil_time {Γ a} (env : Env base Γ) (W : Nat) (hh : header ≤ W) (henv : Q.size (rep.env Γ) env ≤ W)
    (hu : Q.size rep.data.unit () ≤ W) :
    (bound (.nil : Expr Op Γ (.list a))).time env ≤ 3 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hn := lists.nil_le (rep.ty a)
  dsimp only [compileBound, LocalBound.compose, DataCostLaws.unitBound, DataCostLaws.nilBound,
    LanguageRepresentation.ty] at *
  grind only

include lists in
theorem cons_time {Γ a} (hd : Expr Op Γ a) (tl : Expr Op Γ (.list a)) (env : Env base Γ) (W Th Tt : Nat)
    (hh : header ≤ W) (henv : Q.size (rep.env Γ) env ≤ W)
    (hhd : Q.size (rep.ty a) (hd.denote P env) ≤ W) (htl : Q.size (rep.ty (.list a)) (tl.denote P env) ≤ W)
    (th : (bound hd).time env ≤ Th) (tt : (bound tl).time env ≤ Tt) :
    (bound (.cons hd tl)).time env ≤ Th + Tt + 3 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hp := sizes.prod_le (rep.ty a) (rep.ty (.list a)) (hd.denote P env, tl.denote P env)
  have hc := lists.cons_le (rep.ty a) (hd.denote P env) (tl.denote P env)
  dsimp only [compileBound, LocalBound.compose, LocalBound.pair, DataCostLaws.consBound,
    LanguageRepresentation.ty] at *
  grind only

theorem letE_time {Γ a b} (e : Expr Op Γ a) (body : Expr Op (a :: Γ) b) (env : Env base Γ) (W Te Tb : Nat)
    (hh : header ≤ W) (henv : Q.size (rep.env Γ) env ≤ W)
    (he : Q.size (rep.ty a) (e.denote P env) ≤ W)
    (hres : Q.size (rep.ty b) (body.denote P (e.denote P env, env)) ≤ W)
    (te : (bound e).time env ≤ Te) (tb : (bound body).time (e.denote P env, env) ≤ Tb) :
    (bound (.letE e body)).time env ≤ Te + Tb + 3 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hp := sizes.prod_le (rep.ty a) (rep.env Γ) (e.denote P env, env)
  dsimp only [compileBound, LocalBound.compose, LocalBound.pair, LocalBound.identity,
    LanguageRepresentation.env, id] at *
  grind only

theorem op_time {Γ a b} (instr : Op a b) (e : Expr Op Γ a) (env : Env base Γ) (W Te Ti : Nat)
    (henv : Q.size (rep.env Γ) env ≤ W) (he : Q.size (rep.ty a) (e.denote P env) ≤ W)
    (hres : Q.size (rep.ty b) (P.execute instr (e.denote P env)) ≤ W)
    (te : (bound e).time env ≤ Te) (ti : (primitiveBound instr).time (e.denote P env) ≤ Ti) :
    (bound (.op instr e)).time env ≤ Te + Ti + frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  dsimp only [compileBound, LocalBound.compose] at *
  grind only

theorem branch_time {Γ a} (c : Expr Op Γ .bool) (yes no : Expr Op Γ a) (env : Env base Γ) (W Tc Ty Tn : Nat)
    (hh : header ≤ W) (henv : Q.size (rep.env Γ) env ≤ W)
    (hb : ∀ b, Q.size rep.data.bool b ≤ W)
    (hy : Q.size (rep.ty a) (yes.denote P env) ≤ W) (hn : Q.size (rep.ty a) (no.denote P env) ≤ W)
    (tc : (bound c).time env ≤ Tc) (ty : (bound yes).time env ≤ Ty) (tn : (bound no).time env ≤ Tn) :
    (bound (.branch c yes no)).time env ≤ Tc + Ty + Tn + 6 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hp := sizes.prod_le rep.data.bool (rep.env Γ) (c.denote P env, env)
  have hsl := sizes.sum_le (rep.env Γ) (rep.env Γ) (.inl env)
  have hsr := sizes.sum_le (rep.env Γ) (rep.env Γ) (.inr env)
  have hbc := hb (c.denote P env)
  dsimp only [compileBound, LocalBound.compose, LocalBound.pair, LocalBound.identity, LocalBound.elim,
    LocalBound.castFunction, DataCostLaws.selectBound, id, Function.comp_def] at tc ty tn ⊢
  split <;> simp only [Sum.elim_inl, Sum.elim_inr] at hsl hsr ⊢ <;> grind only

/-- A fold: the list and initial accumulator, then the accumulated body work and fold fees. -/
theorem fold_time {Γ a b} (xs : Expr Op Γ (.list a)) (init : Expr Op Γ b) (body : Expr Op (a :: b :: Γ) b)
    (env : Env base Γ) (W Txs Tinit Twork : Nat)
    (hh : header ≤ W) (henv : Q.size (rep.env Γ) env ≤ W)
    (hxs : Q.size (rep.ty (.list a)) (xs.denote P env) ≤ W) (hinit : Q.size (rep.ty b) (init.denote P env) ≤ W)
    (hres : Q.size (rep.ty b) ((xs.denote P env).foldl (fun acc x => body.denote P (x, acc, env)) (init.denote P env)) ≤ W)
    (txs : (bound xs).time env ≤ Txs) (tinit : (bound init).time env ≤ Tinit)
    (twork : foldWork (fun x acc => body.denote P (x, acc, env))
      (fun x acc => (bound body).time (x, acc, env))
      (foldFee (Q := Q) overhead rep.data (rep.ty a) (rep.ty b) (rep.env Γ) (body.denote P) env)
      (xs.denote P env) (init.denote P env) ≤ Twork) :
    (bound (.fold xs init body)).time env ≤ Txs + Tinit + Twork + 4 * frameFee overhead W := by
  have hfee : ∀ k ≤ 16 * W, overhead k ≤ frameFee overhead W := fun _ hk => mono hk
  have hp1 := sizes.prod_le (rep.ty b) (rep.env Γ) (init.denote P env, env)
  have hp2 := sizes.prod_le (rep.ty (.list a)) (StepClass.HasProd.prod (rep.ty b) (rep.env Γ))
    (xs.denote P env, init.denote P env, env)
  dsimp only [compileBound, LocalBound.compose, LocalBound.pair, LocalBound.identity, DataCostLaws.foldBound,
    LanguageRepresentation.ty, LanguageRepresentation.env, id] at *
  grind only

end Signatures.Runtime.BackendProgram.Expression
