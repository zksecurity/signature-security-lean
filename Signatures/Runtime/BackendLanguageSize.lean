import Signatures.Runtime.BackendExpressionSize
import Signatures.Runtime.BackendLanguage

/-! Static description bounds for state-passing compilation. All expressions,
argument frames, effect implementations and context adapters are charged. A
dynamic loop includes its compiled body once; its input counter is runtime data. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.Language

universe v w

variable {Atom : Type} {Op Cmd : Ty Atom → Ty Atom → Type}

def descriptionBound (allowance : Nat)
    (primitiveSize : {a b : Ty Atom} → Op a b → Nat)
    (effectSize : {a b : Ty Atom} → Cmd a b → Nat) {Γ a} : Program Op Cmd Γ a → Nat
  | .ret e => Expression.descriptionBound allowance primitiveSize e + 2
  | .query instr arg => Expression.descriptionBound allowance primitiveSize arg + effectSize instr + 3
  | .bind initial following => descriptionBound allowance primitiveSize effectSize initial +
      descriptionBound allowance primitiveSize effectSize following + 14 * allowance + 6
  | .branch cond yes no => Expression.descriptionBound allowance primitiveSize cond +
      descriptionBound allowance primitiveSize effectSize yes + descriptionBound allowance primitiveSize effectSize no +
      6 * allowance + 3
  | .loop count init body => Expression.descriptionBound allowance primitiveSize count +
      Expression.descriptionBound allowance primitiveSize init + descriptionBound allowance primitiveSize effectSize body +
      28 * allowance + 10
  | .call body args => Expression.argumentsDescription allowance primitiveSize args +
      descriptionBound allowance primitiveSize effectSize body + 3

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {I S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)

include laws

theorem contextInput_size {A E : Type} (a : C.Str A) (e : C.Str E) (store : C.Str S)
    {f : A → E} (context : Q.Realizer a e f) :
    sizes.localSize (contextInput a e store context) ≤ sizes.localSize context + 4 * allowance := by
  refine (laws.pair_bound (laws.identity _)
    (laws.compose_bound (laws.fst _ _) (le_refl (sizes.localSize context)))).trans ?_
  omega

theorem contextReturn_size {B E : Type} (b : C.Str B) (e : C.Str E) (store : C.Str S) :
    sizes.localSize (contextReturn b e store) ≤ 9 * allowance := by
  refine (laws.pair_bound
    (laws.pair_bound (laws.compose_bound (laws.fst _ _) (laws.fst _ _)) (laws.snd _ _))
    (laws.compose_bound (laws.fst _ _) (laws.snd _ _))).trans ?_
  omega

theorem withContext_descriptionSize {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    (store : C.Str S) {f : A → E} (context : Q.Realizer a e f)
    (body : Code Q spec iface (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)) :
    (withContext store context body).descriptionSize sizes ≤
      body.descriptionSize sizes + sizes.localSize context + 13 * allowance + 5 := by
  have hi := contextInput_size sizes allowance laws a e store context
  have ho := contextReturn_size sizes allowance laws b e store
  dsimp only [withContext, Code.descriptionSize]
  omega

variable {base : Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) → Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (primitiveSize : {a b : Ty Atom} → Op a b → Nat)
  (primitiveBound : ∀ {a b} (instr : Op a b), sizes.localSize (primitive instr) ≤ primitiveSize instr)
  (store : C.Str S)

include dataLaws primitiveBound

theorem choose_size {Γ} (cond : Expr Op Γ .bool) :
    sizes.localSize (choose rep data P primitive store cond) ≤
      Expression.descriptionBound allowance primitiveSize cond + 6 * allowance := by
  have he := Expression.compile_size rep data P primitive sizes allowance laws dataLaws primitiveSize primitiveBound cond
  refine (laws.compose_bound
    (laws.pair_bound (laws.compose_bound (laws.fst _ _) he) (laws.identity _)) (dataLaws.select _)).trans ?_
  omega

theorem loopInput_size {Γ a} (count : Expr Op Γ .nat) (init : Expr Op Γ a) :
    sizes.localSize (loopInput rep data P primitive store count init) ≤
      Expression.descriptionBound allowance primitiveSize count +
      Expression.descriptionBound allowance primitiveSize init + 9 * allowance := by
  have hn := Expression.compile_size rep data P primitive sizes allowance laws dataLaws primitiveSize primitiveBound count
  have hi := Expression.compile_size rep data P primitive sizes allowance laws dataLaws primitiveSize primitiveBound init
  refine (laws.pair_bound (laws.compose_bound (laws.fst _ _) hn)
    (laws.pair_bound (laws.pair_bound (laws.compose_bound (laws.fst _ _) hi) (laws.fst _ _)) (laws.snd _ _))).trans ?_
  omega

omit dataLaws primitiveBound in
theorem loopOutput_size {Γ a} :
    sizes.localSize (loopOutput (Γ := Γ) (a := a) rep store) ≤ 5 * allowance := by
  refine (laws.pair_bound (laws.compose_bound (laws.fst _ _) (laws.fst _ _)) (laws.snd _ _)).trans ?_
  omega

variable (effect : {a b : Ty Atom} → Cmd a b →
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store) (StepClass.HasProd.prod (rep.ty b) store))
  (effectSize : {a b : Ty Atom} → Cmd a b → Nat)
  (effectBound : ∀ {a b} (instr : Cmd a b), (effect instr).descriptionSize sizes ≤ effectSize instr)

include effectBound

theorem compile_descriptionSize {Γ a} (source : Program Op Cmd Γ a) :
    (compile rep data P primitive store effect source).descriptionSize sizes ≤
      descriptionBound allowance primitiveSize effectSize source := by
  have he : ∀ {Γ a} (e : Expr Op Γ a), sizes.localSize (Expression.compile rep data P primitive e) ≤
      Expression.descriptionBound allowance primitiveSize e :=
    fun e => Expression.compile_size rep data P primitive sizes allowance laws dataLaws primitiveSize primitiveBound e
  have ha : ∀ {Γ Δ} (args : Args Op Γ Δ), sizes.localSize (Expression.arguments rep data P primitive args) ≤
      Expression.argumentsDescription allowance primitiveSize args :=
    fun args => Expression.arguments_size rep data P primitive sizes allowance laws dataLaws primitiveSize primitiveBound args
  have hc : ∀ {Γ} (cond : Expr Op Γ .bool), sizes.localSize (choose rep data P primitive store cond) ≤
      Expression.descriptionBound allowance primitiveSize cond + 6 * allowance :=
    fun cond => choose_size sizes allowance laws rep data P primitive dataLaws primitiveSize primitiveBound store cond
  have hli : ∀ {Γ a} (count : Expr Op Γ .nat) (init : Expr Op Γ a),
      sizes.localSize (loopInput rep data P primitive store count init) ≤
        Expression.descriptionBound allowance primitiveSize count + Expression.descriptionBound allowance primitiveSize init + 9 * allowance :=
    fun count init => loopInput_size sizes allowance laws rep data P primitive dataLaws primitiveSize primitiveBound store count init
  have hlo : ∀ {Γ a}, sizes.localSize (loopOutput (Γ := Γ) (a := a) rep store) ≤ 5 * allowance :=
    loopOutput_size sizes allowance laws rep store
  have hctx : ∀ {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E} {f : A → E}
      (context : Q.Realizer a e f)
      (body : Code Q spec iface (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)),
      (withContext store context body).descriptionSize sizes ≤
        body.descriptionSize sizes + sizes.localSize context + 13 * allowance + 5 :=
    fun context body => withContext_descriptionSize sizes allowance laws store context body
  have hid := @laws.identity
  have hsnd := @laws.snd
  induction source <;> dsimp only [compile, Code.descriptionSize, descriptionBound] <;> grind only

end Signatures.Runtime.BackendProgram.Language
