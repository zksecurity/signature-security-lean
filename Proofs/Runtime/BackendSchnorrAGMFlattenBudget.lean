import Proofs.Runtime.BackendSchnorrAGMFlatten

/-! Complete native flattening time from scalar/natural-number instruction
contracts. Both list lengths and the retained environment are charged, including
unused coefficient suffixes; no whole-routine budget is assumed. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Flatten

open BackendProgram

private def withRows {Γ : List (Ty CryptoAtom)}
    (prepare : Expr CryptoOp ([scalar, .list affineTy, .list scalar] ++ Γ) rowsTy)
    (finish : Expr CryptoOp ([rowsTy, scalar, .list affineTy, .list scalar] ++ Γ) affineTy) :
    Expr CryptoOp ([.list affineTy, .list scalar] ++ Γ) affineTy :=
  .letE (.op .zero .unit) (.letE prepare finish)

def frameWidth (width basisCap coeffCap : Nat) : Nat := (8 * basisCap + 4 * coeffCap + 32) * width

def flattenTime (overhead : Nat → Nat)
    (width basisCap coeffCap comparisonTime subtractTime incrementTime zeroTime mulTime addTime : Nat) : Nat :=
  let W := frameWidth width basisCap coeffCap
  AttachCompiler.tableTime overhead (3 * width) basisCap coeffCap comparisonTime subtractTime incrementTime +
    zeroTime + sumTime overhead W basisCap mulTime addTime + 64 * overhead (128 * W)

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
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include sizes mono

private theorem withRows_time {Γ : List (Ty CryptoAtom)}
    (prepare : Expr CryptoOp ([scalar, .list affineTy, .list scalar] ++ Γ) rowsTy)
    (finish : Expr CryptoOp ([rowsTy, scalar, .list affineTy, .list scalar] ++ Γ) affineTy)
    (env : Env (cryptoBase F G₁ G₂ K M) ([.list affineTy, .list scalar] ++ Γ))
    (width zeroTime preparationTime finishTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env ([.list affineTy, .list scalar] ++ Γ)) env ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hr : Q.size (rep.ty rowsTy) (prepare.denote (arithmetic F G₁ G₂ K M cost) (0, env)) ≤ width)
    (ho : Q.size (rep.ty affineTy) (finish.denote (arithmetic F G₁ G₂ K M cost)
      (prepare.denote (arithmetic F G₁ G₂ K M cost) (0, env), 0, env)) ≤ width)
    (htz : (primitiveBound .zero).time () ≤ zeroTime)
    (htp : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound prepare).time (0, env) ≤ preparationTime)
    (htf : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound finish).time (prepare.denote (arithmetic F G₁ G₂ K M cost) (0, env), 0, env) ≤ finishTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (withRows prepare finish)).time env ≤
        preparationTime + zeroTime + finishTime + 64 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [withRows, Expression.compileBound, LocalBound.compose, LocalBound.pair,
    LocalBound.identity, DataCostLaws.unitBound, Expr.denote,
    LanguageRepresentation.ty, LanguageRepresentation.env, List.cons_append, List.nil_append] at *
  simp only [show (arithmetic F G₁ G₂ K M cost).execute CryptoOp.zero () = (0 : F) from rfl] at *
  dsimp only [id, Function.comp_def, List.append] at *
  grind only

include lists in
theorem expression_time {Γ : List (Ty CryptoAtom)} (reps : List (F × F)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width basisCap coeffCap comparisonTime subtractTime incrementTime zeroTime mulTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hrc : reps.length ≤ basisCap) (hcc : coeff.length ≤ coeffCap)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hZero : (primitiveBound .zero).time () ≤ zeroTime)
    (hMul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hAdd : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound expression).time (reps, coeff, env) ≤
        flattenTime overhead width basisCap coeffCap comparisonTime subtractTime incrementTime zeroTime mulTime addTime := by
  let W := frameWidth width basisCap coeffCap
  let rows := reps.mapIdx fun n a => (a, (coeff[n]?).getD (0 : F))
  have hw3 : 3 * width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hw : width ≤ W := by omega
  have hp (p : F × F) : Q.size (rep.ty affineTy) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h₁ := hf p.1
    have h₂ := hf p.2
    exact h.trans (by omega)
  have hr (row : (F × F) × F) : Q.size (rep.ty rowTy) row ≤ 5 * width := by
    have h := sizes.prod_le (rep.ty affineTy) (rep.ty scalar) row
    have h₁ := hp row.1
    have h₂ := hf row.2
    exact h.trans (by omega)
  have hreps := lists.size_le_cap (rep.ty affineTy) reps (3 * width) basisCap (fun p _ => hp p) hrc
  have hcoeff := lists.size_le_cap (rep.ty scalar) coeff width coeffCap (fun f _ => hf f) hcc
  have hrowsCount : rows.length ≤ basisCap := by simpa only [rows, List.length_mapIdx] using hrc
  have hrows := lists.size_le_cap (rep.ty rowTy) rows (5 * width) basisCap (fun p _ => hr p) hrowsCount
  have hprod := @sizes.prod_le
  have hrHeader := Nat.mul_le_mul_left basisCap hh
  have hcHeader := Nat.mul_le_mul_left coeffCap hh
  have hinput : Q.size (rep.env ([.list affineTy, .list scalar] ++ Γ)) (reps, coeff, env) ≤ W := by
    dsimp only [W, frameWidth, LanguageRepresentation.env, LanguageRepresentation.ty,
      List.cons_append, List.nil_append] at *
    clear hEq hSub hInc hMul hAdd hf hn
    grind only
  have hrowsSize : Q.size (rep.ty rowsTy) rows ≤ W := by
    dsimp only [W, frameWidth, LanguageRepresentation.ty] at *
    nlinarith
  have hvalue : ((AGM.attachTable (indexTy := affineTy)).weakenTail Γ).denote
      (arithmetic F G₁ G₂ K M cost) (0, reps, coeff, env) = rows :=
    AttachCompiler.table_denote (key := affineTy) (Γ := Γ) cost 0 reps coeff env
  have hprepare := AttachCompiler.table_time_bound (key := affineTy) (Γ := Γ) rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    0 reps coeff env (3 * width) basisCap coeffCap comparisonTime subtractTime incrementTime
    (by omega) (by omega) (by omega) (fun b => (hb b).trans (by omega))
    (fun n hn' => (hn n hn').trans (by omega)) (fun f => (hf f).trans (by omega))
    (fun p _ => hp p) hrc hcc hEq hSub hInc
  have hsum := sumRows_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    rows 0 (Γ := [.list affineTy, .list scalar] ++ Γ) (reps, coeff, env) W basisCap mulTime addTime
    (hh.trans hw) hinput (fun f => (hf f).trans hw) hrowsCount hMul hAdd
  have hfinishSize : Q.size (rep.ty affineTy)
      ((sumRows (Γ := [.list affineTy, .list scalar] ++ Γ)).denote (arithmetic F G₁ G₂ K M cost)
        (rows, 0, reps, coeff, env)) ≤ W := (hp _).trans hw3
  have h := withRows_time (Γ := Γ) rep data cost primitive laws dataLaws primitiveBound sizes mono
    ((AGM.attachTable (indexTy := affineTy)).weakenTail Γ) sumRows (reps, coeff, env) W zeroTime
    (AttachCompiler.tableTime overhead (3 * width) basisCap coeffCap comparisonTime subtractTime incrementTime)
    (sumTime overhead W basisCap mulTime addTime) (hh.trans hw) (hu.trans hw) hinput ((hf 0).trans hw)
    (by rw [hvalue]; exact hrowsSize) (by rw [hvalue]; exact hfinishSize) hZero hprepare
    (by rw [hvalue]; exact hsum)
  exact h

omit mono [Q.HasCategory] QP QS [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [DecidableEq K] [DecidableEq M] in
theorem output_size (reps : List (F × F)) (coeff : List F) (width : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) :
    Q.size (rep.ty affineTy) (value reps coeff) ≤ 3 * width := by
  have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) (value reps coeff)
  have h₁ := hf (value reps coeff).1
  have h₂ := hf (value reps coeff).2
  exact h.trans (by omega)

include laws dataLaws primitiveBound lists in
theorem code_cost {Γ : List (Ty CryptoAtom)} (reps : List (F × F)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width basisCap coeffCap comparisonTime subtractTime incrementTime zeroTime mulTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hrc : reps.length ≤ basisCap) (hcc : coeff.length ≤ coeffCap)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hZero : (primitiveBound .zero).time () ≤ zeroTime)
    (hMul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hAdd : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime) :
    Q.cost (code rep data cost primitive) (reps, coeff, env) ≤
      flattenTime overhead width basisCap coeffCap comparisonTime subtractTime incrementTime zeroTime mulTime addTime := by
  rw [code, QuantitativeStepClass.Realizer.cost_castFunction]
  exact (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound expression (reps, coeff, env)).trans
      (expression_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono reps coeff env
        width basisCap coeffCap comparisonTime subtractTime incrementTime zeroTime mulTime addTime
        hh hu he hb hn hf hrc hcc hEq hSub hInc hZero hMul hAdd)

end Signatures.Runtime.SchnorrAGM.Native.Flatten
