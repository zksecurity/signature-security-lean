import Proofs.Runtime.BackendSchnorrAGMExtractionRoutingBudget
import Proofs.Runtime.BackendSchnorrAGMExtractionDecodedBudget

/-! Complete runtime of the native final extractor, over every output shape.
The accepted and rejected paths, both scans, response retention, rearrangement,
branch distribution and all control transitions are derived from primitives. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Extraction

open BackendProgram

def extractionTime (overhead : Nat → Nat)
    (width cap historyWidth basisCap groupCap rowCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime pointZeroTime : Nat) : Nat :=
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  let fee := overhead (4096 * W)
  HashDispatch.prepareTime overhead W groupCap rowCap pointZeroTime +
    max (decodedTime overhead width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime) (fieldTime + 261 * fee) + 271 * fee

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.HasOption]
  [QD : Q.IsDistributive] [OptionCode (Q := Q)]
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
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)
  (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
  (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
  (hb : ∀ b, Q.size rep.data.bool b ≤ width)
  (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)

include sizes lists laws dataLaws primitiveBound mono routing dispatch hh hu hb hf

private theorem shape_bound
    (body : Code Q unifSpec iface (rep.ty decodedTy) (rep.ty Read.outputTy))
    (bodyTime fieldTime pointZeroTime : Nat)
    (hbody : Bounds control queryCost body
      (DecodedInput (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth) bodyTime)
    (hg0 : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hz0 : (primitiveBound .zero₁).time () ≤ pointZeroTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime) :
    Bounds control queryCost
      (.seq (.atomic (localCode rep data cost primitive startExpression))
        (.seq (.first (rep.ty scalar) (.atomic (HashDispatch.route rep data cost primitive)))
          (.seq (.atomic (QD.distribute (rep.ty Hash.inputTy) (rep.ty Hash.inputTy) (rep.ty scalar)))
            (.branch body (.atomic (localCode rep data cost primitive rejectExpression))))))
      (Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (HashDispatch.prepareTime overhead (frameWidth width cap historyWidth groupCap rowCap coeffCap)
        groupCap rowCap pointZeroTime +
        max bodyTime (fieldTime + 261 * overhead (4096 * frameWidth width cap historyWidth groupCap rowCap coeffCap)) +
        271 * overhead (4096 * frameWidth width cap historyWidth groupCap rowCap coeffCap)) := by
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  let fee := overhead (4096 * W)
  let preparationTime := HashDispatch.prepareTime overhead W groupCap rowCap pointZeroTime
  let pre := Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap
  let started := StartingInput (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap
  let routed := RoutedInput (Q := Q) rep width cap historyWidth basisCap coeffCap
  let decodedPre := DecodedInput (Q := Q) rep width cap historyWidth basisCap coeffCap
  let post := Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  have hframe := hash_frame_le width cap historyWidth groupCap rowCap coeffCap
  have hs := start_bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf
  have hr := route_bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf pointZeroTime hg0 hz0
  have hj := reject_bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf fieldTime hz
  have hparts (input) (hi : decodedPre input) :
      Q.size (rep.ty Hash.inputTy) input.1 ≤ W ∧ Q.size (rep.ty scalar) input.2 ≤ W := by
    have hp := (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf input.1 hi.1).1
    exact ⟨hp.trans hframe, hi.2.trans hw⟩
  have hbranch := branchStore_bound_of_width sizes mono control queryCost routing dispatch (rep.ty scalar)
    body (.atomic (localCode rep data cost primitive rejectExpression)) decodedPre decodedPre post W
    bodyTime (fieldTime + 261 * fee) (hh.trans hw) hparts hparts hbody hj
  have hbranch' : Bounds control queryCost
      (.seq (.atomic (QD.distribute (rep.ty Hash.inputTy) (rep.ty Hash.inputTy) (rep.ty scalar)))
        (.branch body (.atomic (localCode rep data cost primitive rejectExpression))))
      routed post (max bodyTime (fieldTime + 261 * fee) + 4 * fee) := by
    intro input hi z hrun
    have hpre : Sum.elim (fun x => decodedPre (x, input.2)) (fun y => decodedPre (y, input.2)) input.1 := by
      rcases input with ⟨input, saved⟩
      cases input <;> exact hi
    obtain ⟨ho, ht⟩ := hbranch input hpre z hrun
    have hfee := mono (show 32 * W ≤ 4096 * W by omega)
    exact ⟨ho, by dsimp only [fee]; omega⟩
  have htail := Bounds.seq control queryCost _ _ started routed post
    (preparationTime + 4 * fee) (max bodyTime (fieldTime + 261 * fee) + 4 * fee) fee hr hbranch' (by
      intro input hi output ho
      have hin := starting_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi
      have hout := routed_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf output ho
      exact (routing.sequence _ _).trans (mono (by
        change Q.size (rep.ty startingTy) input + Q.size
          (StepClass.HasProd.prod (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (rep.ty scalar)) output ≤ _
        omega)))
  have hall := Bounds.seq control queryCost _ _ pre started post (261 * fee)
    (preparationTime + 4 * fee + (max bodyTime (fieldTime + 261 * fee) + 4 * fee) + fee) fee hs htail (by
      intro input hi output ho
      have hin := input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi
      have hout := starting_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf output ho
      exact (routing.sequence _ _).trans (mono (by
        change Q.size (rep.ty inputTy) input + Q.size (rep.ty startingTy) output ≤ _
        omega)))
  intro input hi z hrun
  obtain ⟨ho, ht⟩ := hall input hi z hrun
  exact ⟨ho, by dsimp only [preparationTime, fee, W] at *; omega⟩

/-- The full executed extractor has a derived bound on both accepted and
malformed outputs. No budget for a finished component or attacker is assumed. -/
theorem bound (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime
      sampleTime divisionTime pointZeroTime : Nat)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (hmul : ∀ a b : F, (primitiveBound .mul).time (a, b) ≤ mulTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True) (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime)
    (hg0 : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hz0 : (primitiveBound .zero₁).time () ≤ pointZeroTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (extractionTime overhead width cap historyWidth basisCap groupCap rowCap coeffCap comparisonTime subtractTime incrementTime
        messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime pointZeroTime) := by
  have hd := decoded_bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono control queryCost routing
    width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime sampleTime
    hh hu hb hn hf hEq hSub hInc hm hg hz hadd hmul heq hd divisionTime hsub hdiv
  exact shape_bound rep data cost primitive sizes lists laws dataLaws primitiveBound mono control queryCost routing dispatch
    width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf (decoded rep data cost primitive sampler)
    _ fieldTime pointZeroTime hd hg0 hz0 hz

end Signatures.Runtime.SchnorrAGM.Native.Extraction
