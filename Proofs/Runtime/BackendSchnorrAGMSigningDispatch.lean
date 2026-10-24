import Proofs.Runtime.BackendSchnorrAGMSigningBudget
import Proofs.Runtime.BackendListEmpty
import Proofs.Runtime.SchnorrAGMReply

/-! Native signing dispatch for all incoming group/coefficient-list shapes.
Group emptiness is computed by an explicit scan. Both branches construct the
scalar/group-list reply; rejection sets malformed and makes no scalar draws. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.SigningDispatch

open BackendProgram

abbrev inputTy : Ty CryptoAtom := .pair (.list point₁) (.pair (.list (.list scalar)) Signing.inputTy)
abbrev preparedTy : Ty CryptoAtom := .pair .bool Signing.inputTy
abbrev outputTy : Ty CryptoAtom := .pair scalarGroupReplyTy stateTy

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

def prepareWith (scan : Expr CryptoOp [.list point₁, inputTy] .bool) :
    Expr CryptoOp [inputTy] preparedTy :=
  .letE (.fst v0) (.letE scan (.pair v0 (.snd (.snd v2))))

def prepareExpression : Expr CryptoOp [inputTy] preparedTy := prepareWith ListEmpty.scan

def prepareValue {F G M : Type}
    (input : List G × List (List F) × G × G × M × EncodedState F G M) :=
  (input.1.isEmpty, input.2.2)

def routeValue {F G M : Type}
    (input : List G × List (List F) × G × G × M × EncodedState F G M) :=
  if (prepareValue input).1 = true then Sum.inl input.2.2 else Sum.inr input.2.2

def wrapValue {F G M : Type} (input : (G × F) × EncodedState F G M) :=
  ((input.1.2, [input.1.1]), input.2)

def wrapExpression : Expr CryptoOp [Signing.outputTy] outputTy :=
  .pair (.pair (.snd (.fst v0)) (.cons (.fst (.fst v0)) .nil)) (.snd v0)

def rejectValue {F G M : Type} [Zero F]
    (input : G × G × M × EncodedState F G M) : (F × List G) × EncodedState F G M :=
  ((0, []), input.2.2.2.1, input.2.2.2.2.1, input.2.2.2.2.2.1, true, input.2.2.2.2.2.2.2)

def rejectExpression : Expr CryptoOp [Signing.inputTy] outputTy :=
  .pair (.pair (.op .zero .unit) .nil)
    (let state := Expr.snd (Expr.snd (Expr.snd v0))
     let metadata := Expr.snd state
     .pair (.fst state) (.pair (.fst metadata) (.pair (.fst (.snd metadata))
       (.pair (.bool true) (.snd (.snd (.snd metadata)))))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem prepareExpression_value (cost : PrimitiveCosts)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    prepareExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = prepareValue input := by
  dsimp only [prepareExpression, prepareWith, Expr.denote, Var.get]
  rw [ListEmpty.denote]
  rfl

theorem wrapExpression_value (cost : PrimitiveCosts)
    (input : Signing.outputTy.Value (cryptoBase F G₁ G₂ K M)) :
    wrapExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = wrapValue input := rfl

theorem rejectExpression_value (cost : PrimitiveCosts)
    (input : Signing.inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    rejectExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = rejectValue input := rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def prepare : Q.Realizer (rep.ty inputTy) (rep.ty preparedTy) prepareValue :=
  (Q.compose (Read.frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive prepareExpression)).castFunction
      (by funext input; exact prepareExpression_value cost input)

def route : Q.Realizer (rep.ty inputTy) (StepClass.HasSum.sum (rep.ty Signing.inputTy) (rep.ty Signing.inputTy))
    routeValue := Q.compose (prepare rep data cost primitive) (data.select (rep.ty Signing.inputTy))

def wrap : Q.Realizer (rep.ty Signing.outputTy) (rep.ty outputTy) wrapValue :=
  (Q.compose (Read.frame rep data Signing.outputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive wrapExpression)).castFunction
      (by funext input; exact wrapExpression_value cost input)

def reject : Q.Realizer (rep.ty Signing.inputTy) (rep.ty outputTy) rejectValue :=
  (Q.compose (Read.frame rep data Signing.inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive rejectExpression)).castFunction
      (by funext input; exact rejectExpression_value cost input)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def accepted : Code Q unifSpec iface (rep.ty Signing.inputTy) (rep.ty outputTy) :=
  .seq (Signing.code rep data cost primitive sampler) (.atomic (wrap rep data cost primitive))

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty outputTy) :=
  .seq (.atomic (route rep data cost primitive))
    (.branch (accepted rep data cost primitive sampler) (.atomic (reject rep data cost primitive)))

theorem denote (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive sampler).denote input =
      if input.1 = [] then wrapValue <$> (Signing.code rep data cost primitive sampler).denote input.2.2
      else pure (rejectValue input.2.2) := by
  rcases input with ⟨groups, rows, decoded⟩
  cases groups <;> simp only [code, accepted, Code.denote, routeValue, prepareValue,
    List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ite_true, ite_false, List.cons_ne_nil,
    pure_bind, bind_pure_comp]

theorem malformed_run (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (invalid : input.1 ≠ []) :
    (code rep data cost primitive sampler).run control queryCost input =
      (code rep data cost primitive other).run control queryCost input := by
  have h : (prepareValue input).1 = false := by
    dsimp only [prepareValue]
    cases hg : input.1 with
    | nil => exact False.elim (invalid hg)
    | cons g gs => rfl
  simp only [code, Code.run, sequenceRun, pure_bind, routeValue, h, Bool.false_eq_true, ↓reduceIte]

theorem source [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (g pk : G₁) (s : State F G₁ M) (m : M) (groups : List G₁) (rows : List (List F)) :
    (fun p => (decodeGroupReply p.1, p.2)) <$>
      (code rep data cost primitive sampler).denote (groups, rows, g, pk, m, encodeState s) =
    (fun p => (p.1, encodeState p.2)) <$>
      (handler g pk ⟨⟨.sign m, fun _ => groups⟩, fun _ => rows⟩).run s := by
  rw [denote]
  cases groups with
  | nil =>
      simp only [ite_true, Functor.map_map]
      exact Signing.source rep data cost primitive sampler hsample s g pk m rows
  | cons R groups =>
      simp only [List.cons_ne_nil, ite_false, map_pure, handler, StateT.run, ne_eq,
        not_false_eq_true, ite_true]
      rfl

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (code rep data cost primitive sampler).descriptionSize sizes ≤
      2 * sampler.descriptionSize sizes + 2 * primitiveSize .zero + primitiveSize .neg +
        2 * primitiveSize .scale₁ + primitiveSize .sub₁ + primitiveSize .messageEq + primitiveSize .point₁Eq +
        3072 * allowance + 64 := by
  have hframe (ty : Ty CryptoAtom) : sizes.localSize (Read.frame rep data ty) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have hp' : sizes.localSize (prepare rep data cost primitive) ≤ 256 * allowance := by
    rw [prepare, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe inputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp prepareExpression)
    refine h.trans ?_
    simp only [prepareExpression, prepareWith, ListEmpty.scan, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hr : sizes.localSize (route rep data cost primitive) ≤ 258 * allowance :=
    (laws.compose_bound hp' (dataLaws.select _)).trans (by omega)
  have hw : sizes.localSize (wrap rep data cost primitive) ≤ 128 * allowance := by
    rw [wrap, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe Signing.outputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp wrapExpression)
    refine h.trans ?_
    simp only [wrapExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hj : sizes.localSize (reject rep data cost primitive) ≤ primitiveSize .zero + 256 * allowance := by
    rw [reject, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe Signing.inputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
        laws dataLaws primitiveSize hp rejectExpression)
    refine h.trans ?_
    simp only [rejectExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hs := Signing.description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  dsimp only [code, accepted, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native.SigningDispatch
