import Signatures.Runtime.BackendSchnorrAGMExtractionSize
import Signatures.Runtime.BackendSchnorrAGMExtractionLocalCost
import Signatures.Runtime.BackendDispatchBudget

/-! Executed setup, shape routing and rejection budgets for final extraction.
Every retained response and full input frame contributes to the control cost. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Extraction

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)
  (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
  (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
  (hb : ∀ b, Q.size rep.data.bool b ≤ width)
  (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)

include sizes lists laws dataLaws primitiveBound mono routing hh hu hb hf

theorem start_bound :
    Bounds control queryCost (.atomic (iface := iface) (localCode rep data cost primitive startExpression))
      (Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap)
      (StartingInput (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap)
      (261 * overhead (4096 * frameWidth width cap historyWidth groupCap rowCap coeffCap)) := by
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  apply Bounds.atomic
  intro input hi
  have hin := input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi
  have hout := starting_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap
    hh hu hb hf (startValue input) hi
  have ht := start_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input (16 * W)
    (by omega) (by omega) hin
  have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty inputTy) input +
    Q.size (rep.ty startingTy) (startValue input) ≤ 4096 * W by omega))
  refine ⟨hi, ?_⟩
  change Q.cost (localCode rep data cost primitive startExpression) input +
    control.localCall (Q.size (rep.ty inputTy) input) (Q.size (rep.ty startingTy) (startValue input)) ≤ _
  have heq : 256 * (16 * W) = 4096 * W := by omega
  rw [heq] at ht
  change _ ≤ 261 * overhead (4096 * W)
  omega

theorem route_bound (pointZeroTime : Nat)
    (hg0 : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hz0 : (primitiveBound .zero₁).time () ≤ pointZeroTime) :
    Bounds control queryCost (.first (rep.ty scalar) (.atomic (iface := iface) (HashDispatch.route rep data cost primitive)))
      (StartingInput (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap)
      (RoutedInput (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (HashDispatch.prepareTime overhead (frameWidth width cap historyWidth groupCap rowCap coeffCap)
        groupCap rowCap pointZeroTime + 4 * overhead (4096 * frameWidth width cap historyWidth groupCap rowCap coeffCap)) := by
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  let fee := overhead (4096 * W)
  let pre := HashDispatch.Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap
  let post := Sum.elim (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
    (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
  let keep := fun z => Q.size (rep.ty scalar) z ≤ width
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  have h := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing (rep.ty scalar)
    (HashDispatch.route rep data cost primitive) pre post keep (2 * W)
    (HashDispatch.prepareTime overhead W groupCap rowCap pointZeroTime + 2 * fee)
    (by
      intro input hi
      have hin := (HashDispatch.input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap
        hh hu hb hf input hi).1
      change _ ≤ W at hin
      omega)
    (by intro saved hs; dsimp only [keep] at hs; omega)
    (by
      intro input hi
      exact ⟨HashDispatch.route_property rep sizes width cap historyWidth basisCap groupCap rowCap coeffCap hh hg0 input hi,
        HashDispatch.route_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf hg0 input hi,
        HashDispatch.route_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
          width cap historyWidth basisCap groupCap rowCap coeffCap pointZeroTime hh hu hb hf hg0 hz0 input hi⟩)
  intro input hi z hrun
  obtain ⟨ho, ht⟩ := h input hi z hrun
  have hfee := mono (show 32 * (2 * W) ≤ 4096 * W by omega)
  exact ⟨ho, by dsimp only [fee, W] at *; omega⟩

theorem reject_bound (fieldTime : Nat) (hz : (primitiveBound .zero).time () ≤ fieldTime) :
    Bounds control queryCost (.atomic (iface := iface) (localCode rep data cost primitive rejectExpression))
      (DecodedInput (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (fieldTime + 261 * overhead (4096 * frameWidth width cap historyWidth groupCap rowCap coeffCap)) := by
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  have hread : Read.frameWidth (3 * width) cap historyWidth ≤ W := by
    dsimp only [W, frameWidth, HashDispatch.frameWidth]; omega
  apply Bounds.atomic
  intro input hi
  have ho := reject_property rep width cap historyWidth basisCap coeffCap (hf 0) input hi
  have hin := decoded_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi
  have hout := (Read.output_size rep sizes lists (3 * width) cap historyWidth (by omega)
    (fun b => (hb b).trans (by omega)) (0, input.1.2.2) ho).trans hread
  have ht := reject_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input (3 * W) fieldTime
    (by omega) (by omega) ((hf 0).trans (by omega)) hin hz
  have hfee := mono (show 256 * (3 * W) ≤ 4096 * W by omega)
  have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty decodedTy) input +
    Q.size (rep.ty Read.outputTy) (0, input.1.2.2) ≤ 4096 * W by omega))
  refine ⟨ho, ?_⟩
  change Q.cost (localCode rep data cost primitive rejectExpression) input +
    control.localCall (Q.size (rep.ty decodedTy) input) (Q.size (rep.ty Read.outputTy) (0, input.1.2.2)) ≤ _
  change _ ≤ fieldTime + 261 * overhead (4096 * W)
  omega

end Signatures.Runtime.SchnorrAGM.Native.Extraction
