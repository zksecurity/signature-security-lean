import Signatures.Runtime.BackendSchnorrRawLookup
import Signatures.Runtime.BackendSchnorrRawUniformLocalCost
import Signatures.Runtime.PolynomialResources

/-! Complete native selected-challenge lookup resources. The accumulator has
fixed shape, and the runtime is bounded by stored tape length and encoded
operand widths, including retention of the original input. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeLookup

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def Invariant (width slotCap : Nat) (acc : Nat × Bool × F) : Prop :=
  acc.1 ≤ slotCap ∧ Q.size (rep.ty scalar) acc.2.2 ≤ width

def InputBound (width cap slotCap : Nat) (input : Nat × List (TapeCell F)) : Prop :=
  input.1 ≤ slotCap ∧ NativeUniform.TapeBound (Q := Q) rep width cap input.2

theorem step_invariant (width slotCap : Nat) (cell : TapeCell F) (acc : Nat × Bool × F)
    (hc : Q.size (rep.ty scalar) cell.2.1 ≤ width)
    (ha : Invariant (Q := Q) rep width slotCap acc) :
    Invariant (Q := Q) rep width slotCap (step acc cell) := by
  by_cases found : acc.2.1 = true <;> by_cases tag : cell.1 = 1 <;> by_cases zero : acc.1 = 0 <;>
    simp only [step, found, tag, zero, Bool.false_eq_true, ↓reduceIte, Invariant] <;>
    exact ⟨by have := ha.1; omega, by first | exact hc | exact ha.2⟩

theorem fold_invariant (width slotCap : Nat) (cells : List (TapeCell F)) (acc : Nat × Bool × F)
    (hc : ∀ cell ∈ cells, Q.size (rep.ty scalar) cell.2.1 ≤ width)
    (ha : Invariant (Q := Q) rep width slotCap acc) :
    Invariant (Q := Q) rep width slotCap (cells.foldl step acc) := by
  induction cells generalizing acc with
  | nil => exact ha
  | cons cell cells ih =>
      exact ih (step acc cell) (fun x hx => hc x (by simp [hx]))
        (step_invariant rep width slotCap cell acc (hc cell (by simp)) ha)

theorem property [Zero F] (width cap slotCap : Nat) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (input : Nat × List (TapeCell F)) (bound : InputBound (Q := Q) rep width cap slotCap input) :
    Q.size (rep.ty scalar) (answer (0 : F) (values (.inr ()) input.2)[input.1]?).2 ≤ width := by
  rw [← read_values, ← fold_answer]
  exact (fold_invariant rep width slotCap input.2 (input.1, false, 0)
    (fun cell member => (bound.2.1 cell member).2.1) ⟨bound.1, hz⟩).2

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes

theorem accumulator_size (width slotCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (acc : Nat × Bool × F) (ha : Invariant (Q := Q) rep width slotCap acc) :
    Q.size (rep.ty accTy) acc ≤ 5 * width := by
  have hp := @sizes.prod_le
  have hc := hn acc.1 ha.1
  have hf := ha.2
  have hbool := hb acc.2.1
  dsimp only [LanguageRepresentation.ty] at *
  grind only

include lists in
theorem input_size (width cap slotCap : Nat) (hh : header ≤ width)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (input : Nat × List (TapeCell F)) (bound : InputBound (Q := Q) rep width cap slotCap input) :
    Q.size (rep.ty inputTy) input ≤ (6 * cap + 3) * width := by
  have ht := NativeUniform.tape_size rep sizes lists width cap hh input.2 bound.2
  have hc := hn input.1 bound.1
  have hp := sizes.prod_le rep.data.nat (rep.ty (.list Replay.Mixed.event)) input
  change Q.size (rep.ty inputTy) input ≤ _ at hp
  nlinarith

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include mono

theorem body_time (cell : TapeCell F) (acc : Nat × Bool × F) (input : Nat × List (TapeCell F))
    (width comparisonTime subtractTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hsubSize : Q.size rep.data.nat (acc.1 - 1) ≤ width)
    (hi : Q.size (rep.env [Replay.Mixed.event, accTy, inputTy]) (cell, acc, input, ()) ≤ width)
    (heq : (primitiveBound .natEq).time (cell.1, 1) ≤ comparisonTime)
    (hzero : (primitiveBound .natEq).time (acc.1, 0) ≤ comparisonTime)
    (hsub : (primitiveBound .natSub).time (acc.1, 1) ≤ subtractTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound body).time
      (cell, acc, input, ()) ≤ 2 * comparisonTime + subtractTime + 512 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases found : acc.2.1 = true <;> by_cases tag : cell.1 = 1 <;> by_cases zero : acc.1 = 0 <;>
    dsimp only [body, Expression.compileBound, Expression.variableBound, LocalBound.compose,
      LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity, LocalBound.elim,
      LocalBound.castFunction, DataCostLaws.selectBound, DataCostLaws.natBound,
      DataCostLaws.boolBound, DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def, Sum.elim] at * <;>
    simp only [found, tag, zero, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at * <;>
    grind only

omit sizes mono in
def frameWidth (width cap : Nat) : Nat := (8 * cap + 32) * width

omit sizes mono in
def expressionTime (overhead : Nat → Nat) (width cap comparisonTime subtractTime zeroTime : Nat) : Nat :=
  let fee := overhead (256 * frameWidth width cap)
  cap * (2 * comparisonTime + subtractTime + 513 * fee) + zeroTime + 128 * fee

include lists

theorem expression_time (width cap slotCap comparisonTime subtractTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (hcompare : ∀ n m, Q.size rep.data.nat n ≤ width → Q.size rep.data.nat m ≤ width →
      (primitiveBound .natEq).time (n, m) ≤ comparisonTime)
    (hsub : ∀ n ≤ slotCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (input : Nat × List (TapeCell F)) (bound : InputBound (Q := Q) rep width cap slotCap input) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      expression).time (input, ()) ≤ expressionTime overhead width cap comparisonTime subtractTime zeroTime := by
  let W := frameWidth width cap
  let fee := overhead (256 * W)
  let inv := Invariant (Q := Q) rep width slotCap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hin := input_size rep sizes lists width cap slotCap hh hn input bound
  have hp := @sizes.prod_le
  have hcontext : Q.size (rep.env [inputTy]) (input, ()) ≤ (6 * cap + 5) * width := by
    have h := sizes.prod_le (rep.ty inputTy) rep.data.unit (input, ())
    dsimp only [LanguageRepresentation.env]
    exact h.trans (by dsimp only; nlinarith)
  have bodyFunction : body.denote (arithmetic F G₁ G₂ K M cost) = fun p => step p.2.1 p.1 := by
    funext p
    obtain ⟨cell, acc, original, ⟨⟩⟩ := p
    exact body_value cost cell acc original
  have hwork := foldWork_bound (fun cell acc => step acc cell)
    (fun cell acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound body).time (cell, acc, input, ()))
    (foldFee (Q := Q) overhead rep.data (rep.ty Replay.Mixed.event) (rep.ty accTy) (rep.env [inputTy])
      (fun p => step p.2.1 p.1) (input, ()))
    (fun cell => cell ∈ input.2) inv (2 * comparisonTime + subtractTime + 512 * fee) fee cap
    (by
      intro cell member acc ha
      have hcell := NativeUniform.cell_size rep sizes width hh cell (bound.2.1 cell member)
      have hacc := accumulator_size rep sizes width slotCap hh hb hn acc ha
      have hroot : Q.size (rep.env [Replay.Mixed.event, accTy, inputTy]) (cell, acc, input, ()) ≤ W := by
        dsimp only [LanguageRepresentation.env, W, frameWidth] at *
        grind only
      exact ⟨body_time rep sizes data cost primitive laws dataLaws primitiveBound mono cell acc input
        W comparisonTime subtractTime (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw)
        (hn0.trans hw) (hn1.trans hw) ((hn (acc.1 - 1) ((Nat.sub_le _ _).trans ha.1)).trans hw) hroot
        (hcompare cell.1 1 (bound.2.1 cell member).1 hn1) (hcompare acc.1 0 (hn acc.1 ha.1) hn0)
        (hsub acc.1 ha.1), step_invariant rep width slotCap cell acc (bound.2.1 cell member).2.1 ha⟩)
    (by
      intro cells hlen hcells acc ha
      have ht := NativeUniform.tape_size rep sizes lists width cap hh cells
        ⟨fun cell member => bound.2.1 cell (hcells cell member), hlen⟩
      have hacc := accumulator_size rep sizes width slotCap hh hb hn acc ha
      have ho := fold_invariant rep width slotCap cells acc
        (fun cell member => (bound.2.1 cell (hcells cell member)).2.1) ha
      have hout := accumulator_size rep sizes width slotCap hh hb hn _ ho
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, fee, W, frameWidth] at *
      grind only)
    input.2 bound.2.2 (fun _ member => member) (input.1, false, 0) ⟨bound.1, hz⟩
  have hf := fold_invariant rep width slotCap input.2 (input.1, false, 0)
    (fun cell member => (bound.2.1 cell member).2.1) ⟨bound.1, hz⟩
  have hout := accumulator_size rep sizes width slotCap hh hb hn _ hf
  have hnInput := hn input.1 bound.1
  have htape := NativeUniform.tape_size rep sizes lists width cap hh input.2 bound.2
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (2 * comparisonTime + subtractTime + 513 * fee) bound.2.2
  dsimp only [expression, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound, Expr.denote, Var.get,
    arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def,
    expressionTime, fee, W, frameWidth] at *
  simp only [bodyFunction]
  grind only

omit sizes lists mono in
def runtimeBound (overhead : Nat → Nat) (width cap comparisonTime subtractTime zeroTime : Nat) : Nat :=
  expressionTime overhead width cap comparisonTime subtractTime zeroTime +
    5 * overhead (256 * frameWidth width cap)

variable {iface : Interface (C := C) unifSpec}
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws routing

theorem bound (width cap slotCap comparisonTime subtractTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (hcompare : ∀ n m, Q.size rep.data.nat n ≤ width → Q.size rep.data.nat m ≤ width →
      (primitiveBound .natEq).time (n, m) ≤ comparisonTime)
    (hsub : ∀ n ≤ slotCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    Bounds control queryCost (code rep data cost primitive (iface := iface))
      (InputBound (Q := Q) rep width cap slotCap)
      (fun output => Q.size (rep.ty scalar) output.2 ≤ width)
      (runtimeBound overhead width cap comparisonTime subtractTime zeroTime) := by
  apply Bounds.atomic
  intro input hi
  let W := frameWidth width cap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have ho := property rep width cap slotCap hz input hi
  have hin : Q.size (rep.ty inputTy) input ≤ W :=
    (input_size rep sizes lists width cap slotCap hh hn input hi).trans
      (by dsimp [W, frameWidth]; nlinarith)
  have hout : Q.size (rep.ty outputTy) (answer (0 : F) (values (.inr ()) input.2)[input.1]?) ≤ 3 * width := by
    have hp := sizes.prod_le rep.data.bool (rep.ty scalar) (answer (0 : F) (values (.inr ()) input.2)[input.1]?)
    have hbool := hb (answer (0 : F) (values (.inr ()) input.2)[input.1]?).1
    change Q.size (rep.ty outputTy) _ ≤ _ at hp
    omega
  have he := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound expression (input, ())).trans
      (expression_time rep sizes lists data cost primitive laws dataLaws primitiveBound mono
        width cap slotCap comparisonTime subtractTime zeroTime hh hu hb hz hn0 hn1 hn hcompare hsub hzero input hi)
  have hc : Q.cost (compiled rep data cost primitive) input ≤
      expressionTime overhead width cap comparisonTime subtractTime zeroTime + 4 * overhead (256 * W) := by
    rw [compiled, QuantitativeStepClass.Realizer.cost_castFunction]
    exact NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono expression input W
      (expressionTime overhead width cap comparisonTime subtractTime zeroTime)
      (hh.trans hw) (hu.trans hw) hin (by rw [expression_value]; omega) he
  have hcall := (routing.localCall _ _).trans
    (mono (show Q.size (rep.ty inputTy) input +
      Q.size (rep.ty outputTy) (answer (0 : F) (values (.inr ()) input.2)[input.1]?) ≤ 256 * W by omega))
  exact ⟨ho, (Nat.add_le_add hc hcall).trans (by dsimp only [runtimeBound, W]; omega)⟩

omit sizes lists laws dataLaws mono routing in
theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width cap comparisonTime subtractTime zeroTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hCompare : PolynomiallyBounded comparisonTime)
    (hSubtract : PolynomiallyBounded subtractTime) (hZero : PolynomiallyBounded zeroTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (cap n)
      (comparisonTime n) (subtractTime n) (zeroTime n)) := by
  unfold runtimeBound expressionTime frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.RawTape.NativeLookup
