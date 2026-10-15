import Signatures.Runtime.BackendSchnorrAGMHashDispatchSize

/-! Derive the dispatcher's local costs from both actual singleton scans,
default construction and structural routing. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HashDispatch

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

private theorem groupWith_time
    (scan : Expr CryptoOp [.list point₁, point₁, inputTy] groupTy)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width time pointZeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [inputTy]) (input, ()) ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (ho : Q.size (rep.ty groupTy) (scan.denote (arithmetic F G₁ G₂ K M cost)
      (input.2.1, 0, input, ())) ≤ width)
    (hz : (primitiveBound .zero₁).time () ≤ pointZeroTime)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scan).time (input.2.1, 0, input, ()) ≤ time) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (groupWith scan)).time (input, ()) ≤ pointZeroTime + time + 64 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [groupWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
    id, Function.comp_def] at *
  have hzero : (arithmetic F G₁ G₂ K M cost).execute CryptoOp.zero₁ () = (0 : G₁) := rfl
  simp only [hzero] at *
  grind only

private theorem rowWith_time
    (scan : Expr CryptoOp [.list (.list scalar), .list scalar, groupTy, inputTy] rowTy)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (group : Bool × G₁) (width time : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hnil : Q.size (rep.ty (.list scalar)) [] ≤ width)
    (hi : Q.size (rep.env [groupTy, inputTy]) (group, input, ()) ≤ width)
    (ho : Q.size (rep.ty rowTy) (scan.denote (arithmetic F G₁ G₂ K M cost)
      (input.2.2.1, [], group, input, ())) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scan).time (input.2.2.1, [], group, input, ()) ≤ time) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (rowWith scan)).time (group, input, ()) ≤ time + 64 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [rowWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
  grind only

private theorem prepareWith_time (groups : Expr CryptoOp [inputTy] groupTy)
    (rows : Expr CryptoOp [groupTy, inputTy] rowTy)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width groupTime rowTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env [inputTy]) (input, ()) ≤ width)
    (hg : Q.size (rep.ty groupTy) (groups.denote (arithmetic F G₁ G₂ K M cost) (input, ())) ≤ width)
    (hr : Q.size (rep.ty rowTy) (rows.denote (arithmetic F G₁ G₂ K M cost)
      (groups.denote (arithmetic F G₁ G₂ K M cost) (input, ()), input, ())) ≤ width)
    (hgt : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound groups).time (input, ()) ≤ groupTime)
    (hrt : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound rows).time (groups.denote (arithmetic F G₁ G₂ K M cost) (input, ()), input, ()) ≤ rowTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (prepareWith groups rows)).time (input, ()) ≤
        groupTime + rowTime + 256 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hleft := sizes.sum_le (rep.env [rowTy, groupTy, inputTy]) (rep.env [rowTy, groupTy, inputTy])
    (.inl (rows.denote (arithmetic F G₁ G₂ K M cost)
      (groups.denote (arithmetic F G₁ G₂ K M cost) (input, ()), input, ()),
      groups.denote (arithmetic F G₁ G₂ K M cost) (input, ()), input, ()))
  have hright := sizes.sum_le (rep.env [rowTy, groupTy, inputTy]) (rep.env [rowTy, groupTy, inputTy])
    (.inr (rows.denote (arithmetic F G₁ G₂ K M cost)
      (groups.denote (arithmetic F G₁ G₂ K M cost) (input, ()), input, ()),
      groups.denote (arithmetic F G₁ G₂ K M cost) (input, ()), input, ()))
  dsimp only [Sum.elim] at hleft hright
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases hflag : (groups.denote (arithmetic F G₁ G₂ K M cost) (input, ())).1 = true <;>
    dsimp only [prepareWith, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get, id, Function.comp_def, Sum.elim] <;>
    simp only [hflag, ite_true] <;>
    dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env] at * <;> grind only

def prepareTime (overhead : Nat → Nat) (width groupCap rowCap pointZeroTime : Nat) : Nat :=
  pointZeroTime + ListSingleton.scanTime overhead (16 * width) groupCap +
    ListSingleton.scanTime overhead (16 * width) rowCap + 512 * overhead (4096 * width)

include laws dataLaws lists in
theorem prepare_cost (width cap historyWidth basisCap groupCap rowCap coeffCap pointZeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hz : (primitiveBound .zero₁).time () ≤ pointZeroTime)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Q.cost (prepare rep data cost primitive) input ≤
      prepareTime overhead (frameWidth width cap historyWidth groupCap rowCap coeffCap) groupCap rowCap pointZeroTime := by
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  let V := 16 * W
  let group := ListSingleton.value (0 : G₁) input.2.1
  let row := ListSingleton.value ([] : List F) input.2.2.1
  have hw : width ≤ W := by
    have h := Nat.mul_le_mul_right width (show 1 ≤
      4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
    dsimp only [W, frameWidth]
    omega
  have hv : width ≤ V := by dsimp [V]; omega
  have hcw : (2 * coeffCap + 1) * width ≤ W := by
    have h := Nat.mul_le_mul_right width (show 2 * coeffCap + 1 ≤
      4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
    dsimp only [W, frameWidth]
    omega
  have hin := input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi
  have hgroup : Q.size (rep.ty groupTy) group ≤ 3 * width :=
    ListSingleton.output_size rep sizes input.2.1 (0 : G₁) width hh hb hg hi.group_size
  have hcoeff := coefficient_size rep lists width coeffCap hh hf
  have hnil : Q.size (rep.ty (.list scalar)) [] ≤ W := (hcoeff [] (by simp)).trans hcw
  have hrows : ∀ r ∈ input.2.2.1, Q.size (rep.ty (.list scalar)) r ≤ W :=
    fun r hr => (hcoeff r (hi.coefficient_length r hr)).trans hcw
  have hrow : Q.size (rep.ty rowTy) row ≤ 3 * W :=
    ListSingleton.output_size rep sizes input.2.2.1 ([] : List F) W (hh.trans hw)
      (fun b => (hb b).trans hw) hnil hrows
  have hp := @sizes.prod_le
  have henv : Q.size (rep.env [groupTy, inputTy]) (group, input, ()) ≤ V := by
    have h := sizes.prod_le (rep.ty groupTy) (rep.env [inputTy]) (group, input, ())
    exact h.trans (by dsimp only [V]; omega)
  have hgs := ListSingleton.scan_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    sizes lists mono (Γ := [inputTy]) input.2.1 (0 : G₁) (input, ()) V groupCap
    (hh.trans hv) (hu.trans hv) (fun b => (hb b).trans hv) (hin.2.trans (by dsimp [V]; omega))
    (hg.trans hv) (fun g hg' => (hi.group_size g hg').trans hv) hi.group_length
  have hrs := ListSingleton.scan_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    sizes lists mono (Γ := [groupTy, inputTy]) input.2.2.1 ([] : List F) (group, input, ()) V rowCap
    (hh.trans hv) (hu.trans hv) (fun b => (hb b).trans hv) henv (hnil.trans (by dsimp [V]; omega))
    (fun r hr => (hrows r hr).trans (by dsimp [V]; omega)) hi.row_length
  have hgt := groupWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    ListSingleton.scan input V (ListSingleton.scanTime overhead V groupCap) pointZeroTime
    (hh.trans hv) (hu.trans hv) (hin.2.trans (by dsimp [V]; omega)) (hg.trans hv)
    (hgroup.trans (by dsimp [V]; omega)) hz hgs
  have hrt := rowWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    ListSingleton.scan input group V (ListSingleton.scanTime overhead V rowCap)
    (hh.trans hv) (hu.trans hv) (hnil.trans (by dsimp [V]; omega)) henv
    (hrow.trans (by dsimp [V]; omega)) hrs
  have he := prepareWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (groupWith ListSingleton.scan) (rowWith ListSingleton.scan) input V
    (pointZeroTime + ListSingleton.scanTime overhead V groupCap + 64 * overhead (256 * V))
    (ListSingleton.scanTime overhead V rowCap + 64 * overhead (256 * V))
    (hh.trans hv) (hu.trans hv) (fun b => (hb b).trans hv) (hin.2.trans (by dsimp [V]; omega))
    (hgroup.trans (by dsimp [V]; omega)) (hrow.trans (by dsimp [V]; omega)) hgt hrt
  have hexpr := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound prepareExpression (input, ())).trans he
  have hout := prepare_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf hg input hi
  rw [prepare, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono prepareExpression input V
    _ (hh.trans hv) (hu.trans hv) (hin.1.trans (by dsimp [V]; omega))
    (by rw [prepareExpression_value]; exact hout.trans (by dsimp [V]; omega)) hexpr
  have hscale : 256 * V = 4096 * W := by dsimp only [V]; omega
  rw [hscale] at h
  exact h.trans (by dsimp only [prepareTime, V, W] at *; omega)

end Signatures.Runtime.SchnorrAGM.Native.HashDispatch
