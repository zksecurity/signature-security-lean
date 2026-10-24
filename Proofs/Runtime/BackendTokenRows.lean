import Proofs.Runtime.BackendAttachTable
import Proofs.Runtime.TokenCoefficients

/-! Native chronological transcript/coefficient matching. Both reversals,
positional scans, zero initialization, and retained contexts have derived
budgets. No finite message universe or complete-routine cost premise is used. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.TokenCompiler

open AGM AttachCompiler

universe v w

private def rowsWith {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (reverse : Expr CryptoOp ([.list key, .list scalar, .list key, .list scalar] ++ Γ) (.list key))
    (table : Expr CryptoOp ([scalar, .list key, .list scalar, .list key, .list scalar] ++ Γ) (tableTy key)) :
    Expr CryptoOp ([.list key, .list scalar] ++ Γ) (tableTy key) :=
  .letE (.var (.there .here))
    (.letE (.letE (.var (.there .here)) reverse) (.letE (.op .zero .unit) table))

def rowsWidth (width tokenCap coeffCap : Nat) : Nat := (4 * tokenCap + 8 * coeffCap + 32) * width

def rowsTime (overhead : Nat → Nat) (width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime : Nat) : Nat :=
  let fee := overhead (128 * tableWidth (rowsWidth width tokenCap coeffCap) tokenCap coeffCap)
  tokenCap * (coeffCap * (comparisonTime + subtractTime + 257 * fee) + addTime + 355 * fee) + zeroTime + 192 * fee

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

private theorem rowsWith_time_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (reverse : Expr CryptoOp ([.list key, .list scalar, .list key, .list scalar] ++ Γ) (.list key))
    (table : Expr CryptoOp ([scalar, .list key, .list scalar, .list key, .list scalar] ++ Γ) (tableTy key))
    (tr : List (key.Value (cryptoBase F G₁ G₂ K M))) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width reverseTime tableTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env ([.list key, .list scalar] ++ Γ)) (tr, coeff, env) ≤ width)
    (hv : Q.size (rep.ty (.list key))
      (reverse.denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, tr, coeff, env)) ≤ width)
    (ho : Q.size (rep.ty (tableTy key))
      (table.denote (arithmetic F G₁ G₂ K M cost)
        (0, reverse.denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, tr, coeff, env), coeff, tr, coeff, env)) ≤ width)
    (hr : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound reverse).time (tr, coeff, tr, coeff, env) ≤ reverseTime)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound table).time
        (0, reverse.denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, tr, coeff, env), coeff, tr, coeff, env) ≤ tableTime)
    (hzero : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (rowsWith reverse table)).time (tr, coeff, env) ≤
        reverseTime + tableTime + zeroTime + 64 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  have hzeroValue : (arithmetic F G₁ G₂ K M cost).execute CryptoOp.zero () = (0 : F) := rfl
  dsimp only [rowsWith, tableTy, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, LanguageRepresentation.env, LanguageRepresentation.ty,
    List.cons_append, List.nil_append, List.append, Expr.denote, Var.get] at *
  simp only [hzeroValue] at *
  grind only

omit sizes mono in
theorem rows_denote {dataTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((tokenRows (dataTy := dataTy)).weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, env) =
      tr.reverse.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff coeff n)) := by
  have h := (tokenRows (dataTy := dataTy)).weakenTail_denote (arithmetic F G₁ G₂ K M cost)
    (tr, coeff, ()) env
  change ((tokenRows (dataTy := dataTy)).weakenTail Γ).denote _ (tr, coeff, env) = _ at h
  rw [h, ← Expr.run_value, tokenRows_value]

include lists in
theorem rows_time_bound {dataTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ tokenCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (tokenTy dataTy)) p ≤ width)
    (htc : tr.length ≤ tokenCap) (hcc : coeff.length ≤ coeffCap)
    (hEq : ∀ n ≤ tokenCap, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ tokenCap, (primitiveBound CryptoOp.natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ tokenCap, (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ addTime)
    (hZero : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound ((tokenRows (dataTy := dataTy)).weakenTail Γ)).time (tr, coeff, env) ≤
        rowsTime overhead width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime := by
  let U := rowsWidth width tokenCap coeffCap
  have hw : width ≤ U := by dsimp [U, rowsWidth]; nlinarith
  have htr := lists.size_le_cap (rep.ty (tokenTy dataTy)) tr width tokenCap hk htc
  have hc := lists.size_le_cap (rep.ty scalar) coeff width coeffCap (fun f _ => hf f) hcc
  have hrev := lists.size_le_cap (rep.ty (tokenTy dataTy)) tr.reverse width tokenCap
    (fun p hp => hk p (List.mem_reverse.mp hp)) (by simpa only [List.length_reverse] using htc)
  have hprod := @sizes.prod_le
  have hth := Nat.mul_le_mul_left tokenCap hh
  have hch := Nat.mul_le_mul_left coeffCap hh
  have henv : Q.size (rep.env ([.list (tokenTy dataTy), .list scalar] ++ Γ)) (tr, coeff, env) ≤ U := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, List.cons_append, List.nil_append, List.append,
      U, rowsWidth] at *
    clear hn hf hEq hSub hAdd
    grind only
  have htail : Q.size (rep.env ([.list scalar, .list (tokenTy dataTy), .list scalar] ++ Γ))
      (coeff, tr, coeff, env) ≤ U := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, List.cons_append, List.nil_append, List.append,
      U, rowsWidth] at *
    clear hn hf hEq hSub hAdd
    grind only
  have hrevSize : Q.size (rep.ty (.list (tokenTy dataTy))) tr.reverse ≤ U := by
    change Q.size (rep.ty (.list (tokenTy dataTy))) tr.reverse ≤ _ at hrev
    dsimp only [U, rowsWidth]; nlinarith
  have htableValue := table_denote (key := tokenTy dataTy)
    (Γ := [.list (tokenTy dataTy), .list scalar] ++ Γ) cost (0 : F) tr.reverse coeff (tr, coeff, env)
  have hrows : Q.size (rep.ty (tableTy (tokenTy dataTy)))
      (tr.reverse.mapIdx (fun n p => (p, (coeff[n]?).getD 0))) ≤ U := by
    have h := rows_encoded_size rep sizes lists (key := tokenTy dataTy)
      (tr.reverse.mapIdx (fun n p => (p, (coeff[n]?).getD 0))) width tokenCap hh hf
      (by
        intro row hr
        obtain ⟨n, hn', rfl⟩ := (List.mem_mapIdx (l := tr.reverse)).mp hr
        exact hk _ (List.mem_reverse.mp (List.getElem_mem hn')))
      (by simpa only [List.length_mapIdx, List.length_reverse] using htc)
    dsimp only [U, rowsWidth]
    nlinarith
  have hreverse := ReverseCompiler.reverse_time_bound rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound sizes lists mono (cell := tokenTy dataTy)
    (Γ := [.list scalar, .list (tokenTy dataTy), .list scalar] ++ Γ)
    tr (coeff, tr, coeff, env) U tokenCap (hh.trans hw) (hu.trans hw) htail
    (fun p hp => (hk p hp).trans hw) htc
  have htable := table_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (key := tokenTy dataTy) (Γ := [.list (tokenTy dataTy), .list scalar] ++ Γ)
    (0 : F) tr.reverse coeff (tr, coeff, env) U tokenCap coeffCap comparisonTime subtractTime addTime
    (hh.trans hw) (hu.trans hw) henv (fun b => (hb b).trans hw) (fun n hn' => (hn n hn').trans hw)
    (fun f => (hf f).trans hw) (fun p hp => (hk p (List.mem_reverse.mp hp)).trans hw)
    (by simpa only [List.length_reverse] using htc) hcc hEq hSub hAdd
  have h := rowsWith_time_bound rep data cost primitive laws dataLaws primitiveBound sizes mono
    (reverseList (cell := tokenTy dataTy) (Γ := [.list scalar, .list (tokenTy dataTy), .list scalar] ++ Γ))
    ((attachTable (indexTy := tokenTy dataTy)).weakenTail ([.list (tokenTy dataTy), .list scalar] ++ Γ))
    tr coeff env U _ (tableTime overhead U tokenCap coeffCap comparisonTime subtractTime addTime)
    zeroTime (hh.trans hw) (hu.trans hw) ((hf 0).trans hw) henv
    (by rw [reverseList_denote]; exact hrevSize)
    (by rw [reverseList_denote, htableValue]; exact hrows) hreverse
    (by rw [reverseList_denote]; exact htable) hZero
  have hsyntax : rowsWith (key := tokenTy dataTy) (Γ := Γ)
      (reverseList (cell := tokenTy dataTy) (Γ := [.list scalar, .list (tokenTy dataTy), .list scalar] ++ Γ))
      ((attachTable (indexTy := tokenTy dataTy)).weakenTail ([.list (tokenTy dataTy), .list scalar] ++ Γ)) =
      (tokenRows (dataTy := dataTy)).weakenTail Γ := rfl
  rw [hsyntax] at h
  have hfw : U ≤ frameWidth U tokenCap coeffCap :=
    Nat.le_mul_of_pos_left U (by omega : 0 < 8 * tokenCap + 4 * coeffCap + 32)
  have harg : U ≤ 4 * frameWidth U tokenCap coeffCap := by omega
  have hbig := Nat.le_mul_of_pos_left (4 * frameWidth U tokenCap coeffCap)
    (by omega : 0 < 4 * tokenCap + 8)
  have hm : overhead (128 * U) ≤ overhead (128 * tableWidth U tokenCap coeffCap) :=
    mono (Nat.mul_le_mul_left 128 (harg.trans hbig))
  have hr : overhead (128 * ((4 * tokenCap + 8) * U)) ≤ overhead (128 * tableWidth U tokenCap coeffCap) :=
    mono (Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left (4 * tokenCap + 8) harg))
  apply h.trans
  dsimp only [rowsTime, tableTime, U] at *
  nlinarith only [hm, hr, Nat.mul_le_mul_left tokenCap hr]

omit mono [Q.HasCategory] QP QS in
include lists in
theorem rows_output_size {dataTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width tokenCap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (tokenTy dataTy)) p ≤ width) (htc : tr.length ≤ tokenCap) :
    Q.size (rep.ty (tokenRowsTy dataTy))
      (((tokenRows (dataTy := dataTy)).weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, env)) ≤
        (4 * tokenCap + 1) * width := by
  rw [rows_denote]
  apply rows_encoded_size rep sizes lists (key := tokenTy dataTy) _ width tokenCap hh hf
  · intro row hr
    obtain ⟨n, hn', rfl⟩ := (List.mem_mapIdx (l := tr.reverse)).mp hr
    exact hk _ (List.mem_reverse.mp (List.getElem_mem hn'))
  · simpa only [List.length_mapIdx, List.length_reverse] using htc

include laws dataLaws primitiveBound lists in
theorem rows_cost_bound {dataTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ tokenCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (tokenTy dataTy)) p ≤ width)
    (htc : tr.length ≤ tokenCap) (hcc : coeff.length ≤ coeffCap)
    (hEq : ∀ n ≤ tokenCap, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ tokenCap, (primitiveBound CryptoOp.natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ tokenCap, (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ addTime)
    (hZero : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      ((tokenRows (dataTy := dataTy)).weakenTail Γ)) (tr, coeff, env) ≤
        rowsTime overhead width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound _ _).trans
    (rows_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono tr coeff env
      width tokenCap coeffCap comparisonTime subtractTime addTime zeroTime hh hu he hb hn hf hk htc hcc hEq hSub hAdd hZero)

omit sizes mono [C.HasOption] in
theorem rows_description {dataTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      ((tokenRows (dataTy := dataTy)).weakenTail Γ)) ≤
        sizes.localSize (primitive CryptoOp.zero) + sizes.localSize (primitive CryptoOp.natEq) +
          sizes.localSize (primitive CryptoOp.natSub) + sizes.localSize (primitive CryptoOp.natAdd) +
            2048 * allowance + 16 := by
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    ((tokenRows (dataTy := dataTy)).weakenTail Γ)
  simp only [Expression.descriptionBound_weakenTail, tokenRows, attachTable, attachFold, attachBody, index, indexBody,
    reverseList, Expression.descriptionBound, Expression.variableDescription] at h
  exact h.trans (by omega)

end Signatures.Runtime.BackendProgram.TokenCompiler
