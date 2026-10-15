import Signatures.Runtime.BackendSchnorrRawFork
import Signatures.Runtime.BackendSchnorrRawLookupCost

/-! Native fork adapter costs. Every copied frame is charged by its encoded
size. The only nonstructural adapter work is scalar/natural comparison. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeFork

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

include sizes laws dataLaws mono

private theorem frame_time {input output : Ty CryptoAtom} (e : Expr CryptoOp [input] output)
    (x : input.Value (cryptoBase F G₁ G₂ K M)) (width time : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty input) x ≤ width)
    (ho : Q.size (rep.ty output) (e.denote (arithmetic F G₁ G₂ K M cost) (x, ())) ≤ 32 * width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound e).time (x, ()) ≤ time) :
    Q.cost (compileLocal rep data cost primitive e) x ≤ time + 4 * overhead (256 * width) :=
  NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono e x width time hh hu hi ho
    ((Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound e (x, ())).trans ht)

include lists in
theorem start_cost {config : Ty CryptoAtom}
    (x : (config).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (config)) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (startExpression config)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty Replay.Mixed.event)
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (startExpression config)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [startExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem firstSelection_cost {config out : Ty CryptoAtom}
    (x : (firstTy config out).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (firstTy config out)) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (firstSelectionExpression config out)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (firstSelectionExpression config out)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [firstSelectionExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem firstChoice_cost {config out : Ty CryptoAtom}
    (x : (Ty.pair choiceTy (firstTy config out)).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (.pair choiceTy (firstTy config out))) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (firstChoiceExpression config out)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (firstChoiceExpression config out)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [firstChoiceExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem fresh_cost {config out : Ty CryptoAtom}
    (x : (selectedTy config out).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (selectedTy config out)) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (freshExpression config out)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (freshExpression config out)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [freshExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem lookup_cost {config out : Ty CryptoAtom}
    (x : (freshTy config out).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (freshTy config out)) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (lookupExpression config out)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (lookupExpression config out)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [lookupExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem reset_cost {config out : Ty CryptoAtom}
    (x : (freshTy config out).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (freshTy config out)) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (resetExpression config out)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (resetExpression config out)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [resetExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem second_cost {config out : Ty CryptoAtom}
    (x : (Ty.pair stateTy (carryTy config out)).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (.pair stateTy (carryTy config out))) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (secondExpression config out)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (secondExpression config out)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [secondExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem secondSelection_cost {out : Ty CryptoAtom}
    (x : (secondTy out).Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty (secondTy out)) x ≤ width) :
    Q.cost (compileLocal rep data cost primitive (secondSelectionExpression out)) x ≤ 516 * overhead (256 * width) := by
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (secondSelectionExpression out)
    x width (512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    dsimp only [secondSelectionExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
    grind only

theorem collision_cost {config out : Ty CryptoAtom}
    (x : (Ty.pair NativeLookup.outputTy (freshTy config out)).Value (cryptoBase F G₁ G₂ K M))
    (width comparisonTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.ty (.pair NativeLookup.outputTy (freshTy config out))) x ≤ width)
    (hc : (primitiveBound .scalarEq).time (x.1.2, x.2.1) ≤ comparisonTime) :
    Q.cost (compileLocal rep data cost primitive (collisionExpression config out)) x ≤
      comparisonTime + 516 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (collisionExpression config out)
    x width (comparisonTime + 512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    by_cases found : x.1.1 = true
    all_goals
      dsimp only [collisionExpression, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
        LocalBound.castFunction, LocalBound.elim, DataCostLaws.selectBound, DataCostLaws.boolBound,
        DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic, Sum.elim,
        LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
      simp only [found, Bool.false_eq_true, ↓reduceIte] at *
      grind only

theorem finish_cost {out : Ty CryptoAtom}
    (x : (Ty.pair choiceTy (secondTy out)).Value (cryptoBase F G₁ G₂ K M))
    (width comparisonTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.ty (.pair choiceTy (secondTy out))) x ≤ width)
    (hc : (primitiveBound .natEq).time (x.1.2, x.2.2.1) ≤ comparisonTime) :
    Q.cost (compileLocal rep data cost primitive (finishExpression out)) x ≤
      comparisonTime + 516 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  refine (frame_time rep data cost primitive sizes laws dataLaws primitiveBound mono (finishExpression out)
    x width (comparisonTime + 512 * overhead (256 * width)) hh hu hi ?_ ?_).trans (by omega)
  all_goals
    by_cases found : x.1.1 = true
    all_goals
      dsimp only [finishExpression, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
        LocalBound.castFunction, LocalBound.elim, DataCostLaws.selectBound, DataCostLaws.boolBound,
        DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic, Sum.elim,
        LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
      simp only [found, Bool.false_eq_true, ↓reduceIte] at *
      grind only

theorem chooseLocal_cost {input output : Ty CryptoAtom} (e : Expr CryptoOp [input] (.pair .bool output))
    (x : input.Value (cryptoBase F G₁ G₂ K M)) (width time : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.ty input) x ≤ width)
    (ho : Q.size (rep.ty (.pair .bool output)) (e.denote (arithmetic F G₁ G₂ K M cost) (x, ())) ≤ width)
    (hc : Q.cost (compileLocal rep data cost primitive e) x ≤ time) :
    Q.cost (chooseLocal rep data cost primitive e) x ≤ time + 2 * overhead (256 * width) := by
  let y := e.denote (arithmetic F G₁ G₂ K M cost) (x, ())
  change Q.size (rep.ty (.pair .bool output)) y ≤ width at ho
  have hy : Q.size (rep.ty output) y.2 ≤ width :=
    (sizes.snd_le rep.data.bool (rep.ty output) y).trans ho
  have hout : Q.size (StepClass.HasSum.sum (rep.ty output) (rep.ty output))
      (if y.1 then Sum.inl y.2 else Sum.inr y.2) ≤ 2 * width := by
    split
    · have hs := sizes.sum_le (rep.ty output) (rep.ty output) (Sum.inl y.2)
      dsimp only [Sum.elim, Sum.rec] at hs
      omega
    · have hs := sizes.sum_le (rep.ty output) (rep.ty output) (Sum.inr y.2)
      dsimp only [Sum.elim, Sum.rec] at hs
      omega
  have hselected := dataLaws.select (rep.ty output) y
  have hcompose := laws.compose (compileLocal rep data cost primitive e) (data.select (rep.ty output)) x
  have hs : Q.cost (data.select (rep.ty output)) y ≤ overhead (256 * width) :=
    hselected.trans (mono (by change Q.size (rep.ty (.pair .bool output)) y + _ ≤ _; omega))
  have hj : overhead (Q.size (rep.ty input) x + Q.size (rep.ty (.pair .bool output)) y +
      Q.size (StepClass.HasSum.sum (rep.ty output) (rep.ty output))
        (if y.1 then Sum.inl y.2 else Sum.inr y.2)) ≤ overhead (256 * width) :=
    mono (by omega)
  exact hcompose.trans (by dsimp only [y] at hs hj; omega)

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem reject_cost (input out : Ty CryptoAtom)
    (x : input.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty input) x ≤ width)
    (hinl : Q.cost (QS.inl rep.data.unit (rep.ty (.pair out out))) () ≤
      overhead (Q.size rep.data.unit () +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inl ()))) :
    Q.cost (reject rep data input out) x ≤ 3 * overhead (256 * width) := by
  have hs := sizes.sum_le rep.data.unit (rep.ty (.pair out out)) (.inl ())
  dsimp only [Sum.elim] at hs
  have hunit := dataLaws.unit (rep.ty input) x
  have ht := laws.compose (data.unit (rep.ty input))
    (QS.inl rep.data.unit (rep.ty (.pair out out))) x
  have huCost := hunit.trans (mono (show Q.size (rep.ty input) x + Q.size rep.data.unit () ≤
    256 * width by omega))
  have hlCost := hinl.trans (mono (show Q.size rep.data.unit () +
    Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inl ()) ≤
      256 * width by omega))
  have hj := mono (show Q.size (rep.ty input) x + Q.size rep.data.unit () +
    Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inl ()) ≤
      256 * width by omega)
  exact ht.trans (by omega)

end Signatures.Runtime.Schnorr.RawTape.NativeFork
