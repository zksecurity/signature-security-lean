import Signatures.Runtime.BackendSchnorrROMExtractionExpressionBudget

/-! Complete runtime of the native guarded extractor. Both fallback paths,
all local calls and branch/sequence controls are charged. The only supplied
whole-code bound is for the actual original sampler. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeExtraction

open BackendProgram RawTape

def runtimeBound (overhead : Nat → Nat)
    (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime sampleTime : Nat) : Nat :=
  localTime overhead width managedCap liveCap pointTime scalarTime subTime divTime zeroTime +
    sampleTime + 16 * overhead (2048 * frameWidth width managedCap liveCap)

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
  {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem code_bound (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (ops : Operations rep cost primitive primitiveBound width pointTime scalarTime subTime divTime zeroTime)
    (hsample : Bounds control queryCost sampler (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ 3 * width) sampleTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (NativeFork.Result (Q := Q) rep (NativeROMFork.controllerWidth width managedCap liveCap)
        (NativeROMFork.ValidOutput (Q := Q) rep width managedCap liveCap))
      (fun f => Q.size (rep.ty scalar) f ≤ 3 * width)
      (runtimeBound overhead width managedCap liveCap pointTime scalarTime subTime divTime zeroTime sampleTime) := by
  let W := frameWidth width managedCap liveCap
  let fee := overhead (256 * (8 * W))
  let localBudget := localTime overhead width managedCap liveCap pointTime scalarTime subTime divTime zeroTime
  have hw : 8 * width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hc : NativeROMFork.controllerWidth width managedCap liveCap ≤ W := by
    dsimp [W, frameWidth, NativeROMFork.controllerWidth]; nlinarith
  let valid := NativeROMFork.ValidOutput (Q := Q) rep width managedCap liveCap
  let unitF : NativeFork.Frame (Q := Q) rep.data.unit W :=
    ⟨fun _ => True, 1, fun u _ => by cases u; simpa using hu.trans (by omega)⟩
  let scalarF : NativeFork.Frame (Q := Q) (rep.ty scalar) W :=
    ⟨fun f => Q.size (rep.ty scalar) f ≤ 3 * width, 1, fun _ h => by simpa using h.trans (by omega)⟩
  let outputF : NativeFork.Frame (Q := Q) (rep.ty NativePass.outputTy) W :=
    ⟨NativeFork.Ready (Q := Q) rep (NativeROMFork.controllerWidth width managedCap liveCap) valid,
      1, fun _ h => by simpa using h.2.trans hc⟩
  let inputF := NativeFork.Frame.pair sizes outputF outputF (by omega : header ≤ W)
  let preF := NativeFork.Frame.sum sizes unitF inputF (by omega : header ≤ W)
  let selectedF := NativeFork.Frame.sum sizes scalarF scalarF (by omega : header ≤ W)
  have unitCap : unitF.factor ≤ 8 := by change 1 ≤ 8; omega
  have scalarCap : scalarF.factor ≤ 8 := by change 1 ≤ 8; omega
  have inputCap : inputF.factor ≤ 8 := by change 3 ≤ 8; omega
  have preCap : preF.factor ≤ 8 := by change 5 ≤ 8; omega
  have selectedCap : selectedF.factor ≤ 8 := by change 3 ≤ 8; omega
  have hselect := NativeFork.Frame.atomic (iface := iface) (cap := 8) mono control queryCost routing
    (NativeFork.chooseLocal rep data cost primitive expression) inputF selectedF localBudget
    inputCap selectedCap (by
      intro input hi
      have hout : Q.size (rep.ty scalar)
          (expression.denote (arithmetic F G₁ G₂ K M cost) (input, ())).2 ≤ 3 * width := by
        rw [expression_denote]
        exact value_scalar rep cost primitive sizes primitiveBound width managedCap liveCap
          pointTime scalarTime subTime divTime zeroTime input.1 input.2 hi.1.1 hi.2.1 hz ops
      change Sum.elim scalarF.property scalarF.property (if _ then _ else _)
      split_ifs <;> exact hout) (by
      intro input hi
      exact expression_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono input.1 input.2
        width managedCap liveCap pointTime scalarTime subTime divTime zeroTime hh hu hb hz hi.1.1 hi.2.1 ops)
  have hidentity := NativeFork.Frame.atomic (iface := iface) (cap := 8) mono control queryCost routing
    (Q.identity (rep.ty scalar)) scalarF scalarF fee scalarCap scalarCap
    (fun _ h => h) (by
      intro f hf
      exact (laws.identity (rep.ty scalar) f).trans (mono (by change _ ≤ 256 * (8 * W); dsimp only [scalarF] at hf; omega)))
  have hunit := NativeFork.Frame.atomic (iface := iface) (cap := 8) mono control queryCost routing
    (data.unit (rep.ty scalar)) scalarF unitF fee scalarCap unitCap
    (fun _ _ => trivial) (by
      intro f hf
      exact (dataLaws.unit (rep.ty scalar) f).trans (mono (by change _ ≤ 256 * (8 * W); dsimp only [scalarF] at hf; omega)))
  have hfallback := NativeFork.Frame.seq (cap := 8) mono control queryCost routing scalarF unitF scalarF
    scalarCap unitCap hunit hsample
  have hbranch := NativeFork.Frame.branch (cap := 8) mono control queryCost routing
    scalarF scalarF selectedF scalarF rfl selectedCap hidentity hfallback
  have hchecked := NativeFork.Frame.seq (cap := 8) mono control queryCost routing inputF selectedF scalarF
    inputCap selectedCap hselect hbranch
  have hall := NativeFork.Frame.branch (cap := 8) mono control queryCost routing unitF inputF preF scalarF
    rfl preCap hsample hchecked
  exact NativeFork.Frame.widen control queryCost hall (by
    dsimp only [runtimeBound, localBudget, fee, W]
    norm_num only [← Nat.mul_assoc]
    omega)

end Signatures.Runtime.Schnorr.ListROM.NativeExtraction
