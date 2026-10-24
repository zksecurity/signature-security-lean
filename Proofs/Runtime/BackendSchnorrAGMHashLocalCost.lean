import Proofs.Runtime.BackendSchnorrAGMHashSize

/-! Charge the actual hash preparation: retaining the original state while
flattening its basis, assembling the read input, and creating the local frame. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Hash

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes mono

private theorem prepareWith_time
    (flatten : Expr CryptoOp [.list affineTy, .list scalar, inputTy] affineTy)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width time : Nat)
    (hh : header ≤ width) (hi : Q.size (rep.env [inputTy]) (input, ()) ≤ width)
    (hf : Q.size (rep.ty affineTy) (flatten.denote (arithmetic F G₁ G₂ K M cost)
      (input.2.2.2.1, input.2.1, input, ())) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound flatten).time (input.2.2.2.1, input.2.1, input, ()) ≤ time) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (prepareWith flatten)).time (input, ()) ≤ time + 256 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [prepareWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
    id, Function.comp_def, List.append] at *
  grind only

include lists laws dataLaws in
theorem prepare_cost (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime fieldTime mulTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hi : Input (Q := Q) rep width cap historyWidth basisCap coeffCap input)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hZero : (primitiveBound .zero).time () ≤ fieldTime)
    (hMul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hAdd : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ fieldTime) :
    Q.cost (prepare rep data cost primitive) input ≤
      Flatten.flattenTime overhead (frameWidth width cap coeffCap historyWidth) basisCap coeffCap
        comparisonTime subtractTime incrementTime fieldTime mulTime fieldTime +
          260 * overhead (256 * frameWidth width cap coeffCap historyWidth) := by
  let W := frameWidth width cap coeffCap historyWidth
  let time := Flatten.flattenTime overhead W basisCap coeffCap comparisonTime subtractTime incrementTime fieldTime mulTime fieldTime
  have hw : width ≤ W := by dsimp [W, frameWidth, Read.frameWidth]; nlinarith
  have h3w : 3 * width ≤ W := by dsimp [W, frameWidth, Read.frameWidth]; nlinarith
  have hsize := input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf input hi
  have hflat := Flatten.expression_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Γ := [inputTy]) input.2.2.2.1 input.2.1 (input, ()) W basisCap coeffCap
    comparisonTime subtractTime incrementTime fieldTime mulTime fieldTime
    (hh.trans hw) (hu.trans hw) hsize.2 (fun b => (hb b).trans hw)
    (fun n hn' => (hn n hn').trans hw) (fun f => (hf f).trans hw) hi.2.2.1 hi.2.2.2
    hEq hSub hInc hZero hMul hAdd
  have hresult := Flatten.output_size rep sizes input.2.2.2.1 input.2.1 width hh hf
  have hexpr := prepareWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    Flatten.expression input W time (hh.trans hw) hsize.2
    (by rw [Flatten.expression_denote]; exact hresult.trans h3w) hflat
  have hcost := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound prepareExpression (input, ())).trans hexpr
  have hout := Read.input_size rep sizes lists (3 * width) cap historyWidth (by omega)
    (fun b => (hb b).trans (by omega)) (prepareValue input)
    (prepare_property rep sizes width cap historyWidth basisCap coeffCap hh hf input hi)
  have hout' : Q.size (rep.ty Read.inputTy) (prepareValue input) ≤ 32 * W := by
    dsimp only [W, frameWidth]
    omega
  rw [prepare, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono prepareExpression input W
    (time + 256 * overhead (256 * W)) (hh.trans hw) (hu.trans hw) hsize.1
    (by rw [prepareExpression_value]; exact hout') hcost
  exact h.trans (by dsimp only [time, W]; omega)

variable {iface : Interface (C := C) unifSpec}
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include lists laws dataLaws routing in
theorem prepare_bound
    (width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime fieldTime mulTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hZero : (primitiveBound .zero).time () ≤ fieldTime)
    (hMul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hAdd : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ fieldTime) :
    Bounds control queryCost (.atomic (iface := iface) (prepare rep data cost primitive))
      (Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (Read.Input (Q := Q) rep (3 * width) cap historyWidth)
      (Flatten.flattenTime overhead (frameWidth width cap coeffCap historyWidth) basisCap coeffCap
        comparisonTime subtractTime incrementTime fieldTime mulTime fieldTime +
          261 * overhead (256 * frameWidth width cap coeffCap historyWidth)) := by
  apply Bounds.atomic
  intro input hi
  have hout := prepare_property rep sizes width cap historyWidth basisCap coeffCap hh hf input hi
  have hin := (input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf input hi).1
  have houtput := Read.input_size rep sizes lists (3 * width) cap historyWidth (by omega)
    (fun b => (hb b).trans (by omega)) (prepareValue input) hout
  have ht := prepare_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    input width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime fieldTime mulTime
    hh hu hb hn hf hi hEq hSub hInc hZero hMul hAdd
  have hc := (routing.localCall _ _).trans (mono (show
    Q.size (rep.ty inputTy) input + Q.size (rep.ty Read.inputTy) (prepareValue input) ≤
      256 * frameWidth width cap coeffCap historyWidth by dsimp only [frameWidth] at *; omega))
  exact ⟨hout, by omega⟩

end Signatures.Runtime.SchnorrAGM.Native.Hash
