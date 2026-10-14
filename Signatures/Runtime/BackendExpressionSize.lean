import Signatures.Runtime.BackendDescriptionLaws

/-! A static bound for every compiled expression and argument frame. Recursive
folds store their executable body once. The bound counts both branch bodies and
all literal/primitive descriptions; it is independent of a particular run. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.Expression

universe v w

variable {Atom : Type} {Op : Ty Atom → Ty Atom → Type}

def variableDescription (allowance : Nat) {Γ a} : Var (Atom := Atom) Γ a → Nat
  | .here => allowance
  | .there v => variableDescription allowance v + 2 * allowance

def descriptionBound (allowance : Nat) (primitiveSize : {a b : Ty Atom} → Op a b → Nat)
    {Γ a} : Expr Op Γ a → Nat
  | .var v => variableDescription allowance v
  | .unit => allowance
  | .bool _ => 3 * allowance
  | .nat n => n + 3 * allowance
  | .pair left right => descriptionBound allowance primitiveSize left + descriptionBound allowance primitiveSize right + allowance
  | .fst pair | .snd pair => descriptionBound allowance primitiveSize pair + 2 * allowance
  | .nil => 3 * allowance
  | .cons head tail => descriptionBound allowance primitiveSize head + descriptionBound allowance primitiveSize tail + 3 * allowance
  | .branch cond yes no => descriptionBound allowance primitiveSize cond + descriptionBound allowance primitiveSize yes +
      descriptionBound allowance primitiveSize no + 6 * allowance
  | .letE value body => descriptionBound allowance primitiveSize value + descriptionBound allowance primitiveSize body + 3 * allowance
  | .op instr arg => descriptionBound allowance primitiveSize arg + primitiveSize instr + allowance
  | .fold values init body => descriptionBound allowance primitiveSize values + descriptionBound allowance primitiveSize init +
      descriptionBound allowance primitiveSize body + 5 * allowance

def argumentsDescription (allowance : Nat) (primitiveSize : {a b : Ty Atom} → Op a b → Nat)
    {Γ Δ} : Args Op Γ Δ → Nat
  | .nil => allowance
  | .cons head tail => descriptionBound allowance primitiveSize head + argumentsDescription allowance primitiveSize tail + allowance

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {base : Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) → Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (primitiveSize : {a b : Ty Atom} → Op a b → Nat)
  (primitiveBound : ∀ {a b} (instr : Op a b), sizes.localSize (primitive instr) ≤ primitiveSize instr)

include laws

theorem variableCode_size {Γ a} (v : Var Γ a) :
    sizes.localSize (variableCode rep v) ≤ variableDescription allowance v := by
  have hc := @laws.compose
  have hf := @laws.fst
  have hs := @laws.snd
  induction v <;> dsimp only [variableCode, variableDescription, Var.get, Function.comp_def,
    LanguageRepresentation.env] at * <;> grind only

include dataLaws primitiveBound

theorem compile_size {Γ a} (e : Expr Op Γ a) :
    sizes.localSize (compile rep data P primitive e) ≤ descriptionBound allowance primitiveSize e := by
  induction e with
  | var v => exact variableCode_size rep sizes allowance laws v
  | unit => exact dataLaws.unit _
  | bool b =>
    refine (laws.compose_bound (dataLaws.unit _) (dataLaws.bool b)).trans ?_
    dsimp only [descriptionBound]; omega
  | nat n =>
    refine (laws.compose_bound (dataLaws.unit _) (dataLaws.nat n)).trans ?_
    dsimp only [descriptionBound]; omega
  | pair left right hl hr => exact laws.pair_bound hl hr
  | fst pair ih =>
    refine (laws.compose_bound ih (laws.fst _ _)).trans ?_
    dsimp only [descriptionBound]; omega
  | snd pair ih =>
    refine (laws.compose_bound ih (laws.snd _ _)).trans ?_
    dsimp only [descriptionBound]; omega
  | nil =>
    refine (laws.compose_bound (dataLaws.unit _) (dataLaws.nil _)).trans ?_
    dsimp only [descriptionBound]; omega
  | cons head tail hh ht =>
    refine (laws.compose_bound (laws.pair_bound hh ht) (dataLaws.cons _)).trans ?_
    dsimp only [descriptionBound]; omega
  | branch cond yes no hc hy hn =>
    dsimp only [compile]
    rw [DescriptionSize.castFunction]
    refine (laws.compose_bound
      (laws.compose_bound (laws.pair_bound hc (laws.identity _)) (dataLaws.select _))
      (laws.elim_bound hy hn)).trans ?_
    dsimp only [descriptionBound]; omega
  | letE value body hv hb =>
    refine (laws.compose_bound (laws.pair_bound hv (laws.identity _)) hb).trans ?_
    dsimp only [descriptionBound]; omega
  | op instr arg ih => exact laws.compose_bound ih (primitiveBound instr)
  | fold values init body hv hi hb =>
    refine (laws.compose_bound (laws.pair_bound hv (laws.pair_bound hi (laws.identity _)))
      ((dataLaws.fold _ _ _ _).trans (Nat.add_le_add_right hb allowance))).trans ?_
    dsimp only [descriptionBound]; omega

theorem arguments_size {Γ Δ} (args : Args Op Γ Δ) :
    sizes.localSize (arguments rep data P primitive args) ≤ argumentsDescription allowance primitiveSize args := by
  induction args with
  | nil => exact dataLaws.unit _
  | cons head tail ih =>
    have hh := compile_size rep data P primitive sizes allowance laws dataLaws primitiveSize primitiveBound head
    have hp := laws.pair (compile rep data P primitive head) (arguments rep data P primitive tail)
    dsimp only [arguments, argumentsDescription, Args.denote, LanguageRepresentation.env] at *
    omega

end Signatures.Runtime.BackendProgram.Expression
