import Proofs.Runtime.BackendAttachTableFold

/-! Complete native positional coefficient attachment. The constructed program
executes the attachment fold and reverses its accumulated rows. Time includes
both traversals, retained contexts, and all structural operations. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.AttachCompiler

open AGM

universe v w

private def tableWith {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (fold : Expr CryptoOp ([scalar, .list key, .list scalar] ++ Γ) (attachState key))
    (reverse : Expr CryptoOp ([tableTy key, attachState key, scalar, .list key, .list scalar] ++ Γ) (tableTy key)) :
    Expr CryptoOp ([scalar, .list key, .list scalar] ++ Γ) (tableTy key) :=
  .letE fold (.letE (.snd (.var .here)) reverse)

def tableWidth (width keyCap coeffCap : Nat) : Nat :=
  (4 * keyCap + 8) * (4 * frameWidth width keyCap coeffCap)

def tableTime (overhead : Nat → Nat) (width keyCap coeffCap comparisonTime subtractTime addTime : Nat) : Nat :=
  let fee := overhead (128 * tableWidth width keyCap coeffCap)
  keyCap * (coeffCap * (comparisonTime + subtractTime + 257 * fee) + addTime + 338 * fee) + 96 * fee

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

private theorem tableWith_time_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (fold : Expr CryptoOp ([scalar, .list key, .list scalar] ++ Γ) (attachState key))
    (reverse : Expr CryptoOp ([tableTy key, attachState key, scalar, .list key, .list scalar] ++ Γ) (tableTy key))
    (env : Env (cryptoBase F G₁ G₂ K M) ([scalar, .list key, .list scalar] ++ Γ))
    (width foldTime reverseTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env ([scalar, .list key, .list scalar] ++ Γ)) env ≤ width)
    (hf : Q.size (rep.ty (attachState key)) (fold.denote (arithmetic F G₁ G₂ K M cost) env) ≤ width)
    (ho : Q.size (rep.ty (tableTy key))
      (reverse.denote (arithmetic F G₁ G₂ K M cost)
        ((fold.denote (arithmetic F G₁ G₂ K M cost) env).2,
          fold.denote (arithmetic F G₁ G₂ K M cost) env, env)) ≤ width)
    (htf : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound fold).time env ≤ foldTime)
    (htr : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound reverse).time ((fold.denote (arithmetic F G₁ G₂ K M cost) env).2,
        fold.denote (arithmetic F G₁ G₂ K M cost) env, env) ≤ reverseTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (tableWith fold reverse)).time env ≤ foldTime + reverseTime + 32 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [tableWith, attachState, tableTy, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    LanguageRepresentation.env, LanguageRepresentation.ty, List.cons_append, List.nil_append, List.append,
    Expr.denote, Var.get] at *
  grind only

omit sizes mono in
theorem fold_denote {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((attachFold (indexTy := key)).weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost)
      (default, keys, values, env) = keys.foldl (attachStep default values) (0, []) := by
  have h := (attachFold (indexTy := key)).weakenTail_denote (arithmetic F G₁ G₂ K M cost)
    (default, keys, values, ()) env
  change ((attachFold (indexTy := key)).weakenTail Γ).denote _ (default, keys, values, env) = _ at h
  rw [h, ← Expr.run_value, attachFold_value, attachStep_fold]
  simp only [Nat.zero_add, List.append_nil]

omit sizes mono in
theorem table_denote {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((attachTable (indexTy := key)).weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost)
      (default, keys, values, env) = keys.mapIdx (fun n i => (i, (values[n]?).getD default)) := by
  have h := (attachTable (indexTy := key)).weakenTail_denote (arithmetic F G₁ G₂ K M cost)
    (default, keys, values, ()) env
  change ((attachTable (indexTy := key)).weakenTail Γ).denote _ (default, keys, values, env) = _ at h
  rw [h, ← Expr.run_value, attachTable_value]

include lists in
theorem table_time_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width keyCap coeffCap comparisonTime subtractTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ keyCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ i ∈ keys, Q.size (rep.ty key) i ≤ width)
    (hkc : keys.length ≤ keyCap) (hvc : values.length ≤ coeffCap)
    (hEq : ∀ n ≤ keyCap, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ keyCap, (primitiveBound CryptoOp.natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ keyCap, (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound ((attachTable (indexTy := key)).weakenTail Γ)).time (default, keys, values, env) ≤
        tableTime overhead width keyCap coeffCap comparisonTime subtractTime addTime := by
  let W := frameWidth width keyCap coeffCap
  let acc := keys.foldl (attachStep default values) (0, [])
  let valid := fun i : key.Value (cryptoBase F G₁ G₂ K M) => Q.size (rep.ty key) i ≤ width
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hacc : Remaining valid keyCap 0 acc :=
    remaining_fold valid keyCap default values keys hk (0, []) ⟨by simpa, by simpa, by simp⟩
  have hs := state_encoded_size rep sizes lists acc width keyCap hh hf
    (hn acc.1 (by have := hacc.1; omega)) hacc.2.2 (by have := hacc.2.1; omega)
  have hsW : Q.size (rep.ty (attachState key)) acc ≤ W := by
    dsimp only [W, frameWidth]; nlinarith
  have hrows : ∀ row ∈ acc.2, Q.size (rep.ty (.pair key scalar)) row ≤ 3 * width := by
    intro row hr
    have h := sizes.prod_le (rep.ty key) (rep.ty scalar) row
    have hi := hacc.2.2 row hr
    have hf' := hf row.2
    change Q.size (rep.ty (.pair key scalar)) row ≤ _ at h
    dsimp only [valid] at hi
    omega
  have ho := rows_encoded_size rep sizes lists acc.2.reverse width keyCap hh hf
    (fun row hr => hacc.2.2 row (List.mem_reverse.mp hr))
    (by simp only [List.length_reverse]; have := hacc.2.1; omega)
  have hoW : Q.size (rep.ty (tableTy key)) acc.2.reverse ≤ W := by
    dsimp only [W, frameWidth]; nlinarith
  have hkeys := lists.size_le_cap (rep.ty key) keys width keyCap hk hkc
  have hvalues := lists.size_le_cap (rep.ty scalar) values width coeffCap (fun f _ => hf f) hvc
  have hd := hf default
  have hprod := @sizes.prod_le
  have hkh := Nat.mul_le_mul_left keyCap hh
  have hvh := Nat.mul_le_mul_left coeffCap hh
  have henv : Q.size (rep.env ([scalar, .list key, .list scalar] ++ Γ))
      (default, keys, values, env) ≤ W := by
    dsimp only [W, frameWidth, LanguageRepresentation.env, LanguageRepresentation.ty,
      List.cons_append, List.nil_append, List.append] at *
    clear hn hf hEq hSub hAdd
    grind only
  have htail : Q.size (rep.env ([attachState key, scalar, .list key, .list scalar] ++ Γ))
      (acc, default, keys, values, env) ≤ 4 * W := by
    have h := sizes.prod_le (rep.ty (attachState key))
      (rep.env ([scalar, .list key, .list scalar] ++ Γ)) (acc, default, keys, values, env)
    change Q.size (rep.env ([attachState key, scalar, .list key, .list scalar] ++ Γ))
      (acc, default, keys, values, env) ≤ _ at h
    dsimp only at h
    omega
  have hfold := fold_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    default keys values env width keyCap coeffCap comparisonTime subtractTime addTime hh hu he hb hn hf hk hkc hvc
    hEq hSub hAdd
  have hreverse := ReverseCompiler.reverse_time_bound rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound sizes lists mono (cell := .pair key scalar)
    (Γ := [attachState key, scalar, .list key, .list scalar] ++ Γ)
    acc.2 (acc, default, keys, values, env) (4 * W) keyCap (by omega) (by omega) htail
    (fun row hr => (hrows row hr).trans (by omega)) (by have := hacc.2.1; omega)
  have hfd : ((attachFold (indexTy := key)).weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost)
      (default, keys, values, env) = acc := fold_denote cost default keys values env
  have h := tableWith_time_bound rep data cost primitive laws dataLaws primitiveBound sizes mono
    ((attachFold (indexTy := key)).weakenTail Γ)
    (reverseList (cell := .pair key scalar) (Γ := [attachState key, scalar, .list key, .list scalar] ++ Γ))
    (default, keys, values, env) W _ _ (hh.trans hw) henv
    (by rw [hfd]; exact hsW)
    (by rw [hfd, reverseList_denote]; exact hoW) hfold
    (by simpa only [hfd] using hreverse)
  change (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound ((attachTable (indexTy := key)).weakenTail Γ)).time (default, keys, values, env) ≤ _ at h
  have hm : overhead (128 * W) ≤ overhead (128 * tableWidth width keyCap coeffCap) :=
    mono (by dsimp only [tableWidth, W]; nlinarith)
  apply h.trans
  dsimp only [tableTime, tableWidth, W] at *
  nlinarith [Nat.mul_le_mul_left keyCap hm, Nat.mul_le_mul_left (keyCap * coeffCap) hm]

include laws dataLaws primitiveBound lists in
theorem table_cost_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width keyCap coeffCap comparisonTime subtractTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ keyCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ i ∈ keys, Q.size (rep.ty key) i ≤ width)
    (hkc : keys.length ≤ keyCap) (hvc : values.length ≤ coeffCap)
    (hEq : ∀ n ≤ keyCap, (primitiveBound CryptoOp.natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ keyCap, (primitiveBound CryptoOp.natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ keyCap, (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ addTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      ((attachTable (indexTy := key)).weakenTail Γ)) (default, keys, values, env) ≤
        tableTime overhead width keyCap coeffCap comparisonTime subtractTime addTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound _ _).trans
    (table_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      default keys values env width keyCap coeffCap comparisonTime subtractTime addTime hh hu he hb hn hf hk hkc hvc
      hEq hSub hAdd)

omit sizes mono [C.HasOption] in
theorem table_description {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      ((attachTable (indexTy := key)).weakenTail Γ)) ≤
        sizes.localSize (primitive CryptoOp.natEq) + sizes.localSize (primitive CryptoOp.natSub) +
          sizes.localSize (primitive CryptoOp.natAdd) + 1024 * allowance + 8 := by
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    ((attachTable (indexTy := key)).weakenTail Γ)
  simp only [Expression.descriptionBound_weakenTail, attachTable, attachFold, attachBody, index, indexBody,
    reverseList, Expression.descriptionBound, Expression.variableDescription] at h
  exact h.trans (by omega)

end Signatures.Runtime.BackendProgram.AttachCompiler
