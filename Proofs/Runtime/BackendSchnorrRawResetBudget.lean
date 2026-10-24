import Proofs.Runtime.BackendSchnorrRawResetCost
import Proofs.Runtime.PolynomialResources

/-! Complete native reset resources. The all-path bound is for the actual
program, with both output tapes charged. The runtime depends polynomially on
encoded widths, stored tape capacities and primitive costs, without a numeric
reset-position factor. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeReset

open BackendProgram

def runtimeBound (overhead : Nat → Nat)
    (width savedCap remainingCap comparisonTime subtractTime : Nat) : Nat :=
  localTime overhead width savedCap remainingCap comparisonTime subtractTime +
    overhead (256 * frameWidth width savedCap remainingCap)

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (width savedCap remainingCap slotCap comparisonTime subtractTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (hcompare : ∀ n m, Q.size rep.data.nat n ≤ width → Q.size rep.data.nat m ≤ width →
      (primitiveBound .natEq).time (n, m) ≤ comparisonTime)
    (hsub : ∀ n ≤ slotCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime) :
    Bounds control queryCost (code rep data cost primitive (iface := iface))
      (InputBound (Q := Q) rep width savedCap remainingCap slotCap)
      (NativeUniform.StateBound (Q := Q) rep width (savedCap + 1) (savedCap + 1))
      (runtimeBound overhead width savedCap remainingCap comparisonTime subtractTime) := by
  apply Bounds.atomic
  intro input hi
  have ho := property rep width savedCap remainingCap slotCap hn0 hn1 input hi
  have hin := input_size rep sizes lists width savedCap remainingCap slotCap hh hn input hi
  have hout := output_size rep sizes lists width savedCap remainingCap slotCap hh hn0 hn1 input hi
  have ht := compiled_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    width savedCap remainingCap slotCap comparisonTime subtractTime hh hu hb hn0 hn1 hn hcompare hsub input hi
  have hc := (routing.localCall _ _).trans
    (mono (show Q.size (rep.ty inputTy) input + Q.size (rep.ty stateTy) (value input) ≤
      256 * frameWidth width savedCap remainingCap by dsimp [frameWidth]; nlinarith))
  exact ⟨ho, Nat.add_le_add ht hc⟩

omit sizes lists laws dataLaws mono routing in
theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width savedCap remainingCap comparisonTime subtractTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hSaved : PolynomiallyBounded savedCap) (hRemaining : PolynomiallyBounded remainingCap)
    (hCompare : PolynomiallyBounded comparisonTime) (hSubtract : PolynomiallyBounded subtractTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (savedCap n) (remainingCap n)
      (comparisonTime n) (subtractTime n)) := by
  unfold runtimeBound localTime frameWidth SeedTape.NativeReset.resetTime
    SeedTape.NativeReset.forwardTime SeedTape.NativeReset.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.RawTape.NativeReset
