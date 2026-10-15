import Signatures.Runtime.BackendSchnorrAGMEntryReadBudget
import Signatures.Runtime.BackendSchnorrAGMHashDispatchBudget
import Signatures.Runtime.BackendSchnorrAGMInterface

/-! Executable final extraction for every Schnorr AGM output shape. Both lists
are scanned, the response scalar is retained across a single cache read, and
the actual cached affine entry supplies the field extraction. Rejected shapes
return zero and preserve the state. All adapters are compiled local code. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.Extraction

open BackendProgram

abbrev inputTy : Ty CryptoAtom := .pair Interface.forgeryTy stateTy
abbrev startingTy : Ty CryptoAtom := .pair HashDispatch.inputTy scalar
abbrev decodedTy : Ty CryptoAtom := .pair Hash.inputTy scalar
abbrev terminalTy : Ty CryptoAtom := .pair EntryRead.outputTy scalar

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here

def startExpression : Expr CryptoOp [inputTy] startingTy :=
  let out := Expr.fst v0
  .pair (.pair (.fst (.fst out))
    (.pair (.fst (.snd out)) (.pair (.snd (.snd out)) (.snd v0)))) (.snd (.fst out))

def startValue {F G M : Type} (input : Interface.Args (M × F) F G × EncodedState F G M) :=
  ((input.1.1.1, input.1.2.1, input.1.2.2, input.2), input.1.1.2)

def solutionValue {F : Type} [Field F] (entry : EncodedEntry F) (z : F) : F :=
  if entry.2.1 then (z - entry.2.2.1) / (entry.2.2.2 + entry.1) else 0

def finishValue {F G M : Type} [Field F] (input : (EncodedEntry F × EncodedState F G M) × F) :=
  (solutionValue input.1.1 input.2, input.1.2)

def finishExpression : Expr CryptoOp [terminalTy] Read.outputTy :=
  let entry := Expr.fst (Expr.fst v0)
  let affine := Expr.snd (Expr.snd entry)
  .pair (.branch (.fst (.snd entry))
    (.op .div (.pair (.op .sub (.pair (.snd v0) (.fst affine)))
      (.op .add (.pair (.snd affine) (.fst entry))))) (.op .zero .unit))
    (.snd (.fst v0))

def rejectExpression : Expr CryptoOp [decodedTy] Read.outputTy :=
  .pair (.op .zero .unit) (.snd (.snd (.fst v0)))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem finishExpression_value (cost : PrimitiveCosts)
    (input : terminalTy.Value (cryptoBase F G₁ G₂ K M)) :
    finishExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = finishValue input := rfl

omit [DecidableEq F] in
theorem solution_encode (entry : Reduction.Entry F) (z : F) :
    solutionValue (encodeEntry entry) z = entrySolution z entry := by
  cases entry with | mk c a => cases a <;> rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def localCode {a b : Ty CryptoAtom} (expression : Expr CryptoOp [a] b) :
    Q.Realizer (rep.ty a) (rep.ty b) (fun input => expression.denote (arithmetic F G₁ G₂ K M cost) (input, ())) :=
  Q.compose (Read.frame rep data a)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive expression)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def prepared : Code Q unifSpec iface (rep.ty Hash.inputTy) (rep.ty EntryRead.outputTy) :=
  .seq (.atomic (Hash.prepare rep data cost primitive)) (EntryRead.code rep data cost primitive sampler)

def decoded : Code Q unifSpec iface (rep.ty decodedTy) (rep.ty Read.outputTy) :=
  .seq (.first (rep.ty scalar) (prepared rep data cost primitive sampler))
    (.atomic (localCode rep data cost primitive finishExpression))

theorem decoded_denote (input : Hash.inputTy.Value (cryptoBase F G₁ G₂ K M)) (z : F) :
    (decoded rep data cost primitive sampler).denote (input, z) =
      (fun p => (solutionValue p.1 z, p.2)) <$>
        (EntryRead.code rep data cost primitive sampler).denote (Hash.prepareValue input) := by
  simp only [decoded, prepared, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

variable [QD : Q.IsDistributive]

def branches : Code Q unifSpec iface
    (StepClass.HasProd.prod (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (rep.ty scalar))
    (rep.ty Read.outputTy) :=
  .seq (.atomic (QD.distribute (rep.ty Hash.inputTy) (rep.ty Hash.inputTy) (rep.ty scalar)))
    (.branch (decoded rep data cost primitive sampler)
      (.atomic (localCode rep data cost primitive rejectExpression)))

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty Read.outputTy) :=
  .seq (.atomic (localCode rep data cost primitive startExpression))
    (.seq (.first (rep.ty scalar) (.atomic (HashDispatch.route rep data cost primitive)))
      (branches rep data cost primitive sampler))

theorem denote (out : Interface.Args (M × F) F G₁) (saved : EncodedState F G₁ M) :
    (code rep data cost primitive sampler).denote (out, saved) =
      match out.2.1, out.2.2 with
      | [R], [coeff] => (decoded rep data cost primitive sampler).denote (((out.1.1, R), coeff, saved), out.1.2)
      | _, _ => pure (0, saved) := by
  rcases out with ⟨⟨m, z⟩, groups, rows⟩
  rcases groups with _ | ⟨R, _ | ⟨R', gs⟩⟩
  · simp [code, branches, Code.denote, startExpression, rejectExpression,
      Expr.denote, Var.get, HashDispatch.routeValue, HashDispatch.prepareValue, arithmetic]
  · rcases rows with _ | ⟨coeff, _ | ⟨coeff', cs⟩⟩ <;>
      simp [code, branches, Code.denote, startExpression, rejectExpression,
        Expr.denote, Var.get, HashDispatch.routeValue, HashDispatch.prepareValue, arithmetic,
        ListSingleton.value_multiple]
  · simp [code, branches, Code.denote, startExpression, rejectExpression,
      Expr.denote, Var.get, HashDispatch.routeValue, HashDispatch.prepareValue, arithmetic,
      ListSingleton.value_multiple]

theorem malformed_run (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (invalid : (HashDispatch.prepareValue (startValue input).1).1 = false) :
    (code rep data cost primitive sampler).run control queryCost input =
      (code rep data cost primitive other).run control queryCost input := by
  simp only [code, branches, Code.run, sequenceRun, retainRun, chargeRun, pure_bind, map_pure,
    HashDispatch.routeValue]
  simp only [show startExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = startValue input from rfl,
    invalid, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem source [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (out : Interface.SourceForgery F G₁ M) (s : State F G₁ M) :
    (code rep data cost primitive sampler).denote (Interface.encodeForgery out, encodeState s) =
      (fun p => (p.1, encodeState p.2)) <$> (finishScalar out).run s := by
  rcases out with ⟨⟨⟨m, z⟩, groups⟩, rows⟩
  rw [denote]
  dsimp only [Interface.encodeForgery]
  rcases hg : groups () with _ | ⟨R, _ | ⟨R', gs⟩⟩
  · simp [finishScalar, hg, StateT.run_pure]
  · rcases hr : rows () with _ | ⟨coeff, _ | ⟨coeff', cs⟩⟩
    · simp [finishScalar, hg, hr, StateT.run_pure]
    · change (decoded rep data cost primitive sampler).denote (((m, R), coeff, encodeState s), z) = _
      rw [decoded_denote]
      have hp : Hash.prepareValue ((m, R), coeff, encodeState s) =
          ((m, R), encodeAffine (flatten coeff s.representations), encodeState s) := by
        change ((m, R), Flatten.value (s.representations.map encodeAffine) coeff, encodeState s) = _
        rw [Flatten.value_source]
      rw [hp]
      rw [EntryRead.source rep data cost primitive sampler hsample s (m, R) (flatten coeff s.representations)]
      simp only [finishScalar, hg, hr, StateT.run_bind, StateT.run_get,
        StateT.run_map, pure_bind, bind_pure_comp, Functor.map_map, solution_encode]
    · simp [finishScalar, hg, hr, StateT.run_pure]
  · simp [finishScalar, hg, StateT.run_pure]

/-- Exact scalar/state projection of the original final verification/extraction. -/
theorem source_finish [SampleableType F] (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (g pk : G₁) (out : Interface.SourceForgery F G₁ M) (s : State F G₁ M) :
    (code rep data cost primitive sampler).denote (Interface.encodeForgery out, encodeState s) =
      (fun p => (p.1.2, encodeState p.2)) <$> (SchnorrAGM.finish g pk out).run s := by
  rw [source rep data cost primitive sampler hsample, finishScalar_eq g pk]
  simp only [Functor.map_map]

end Signatures.Runtime.SchnorrAGM.Native.Extraction
