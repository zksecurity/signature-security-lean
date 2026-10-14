import Signatures.Runtime.BackendAttachTableCost
import Signatures.Runtime.BackendAttachTableState

/-! Complete native budget for the coefficient-attachment fold. The loop
certificate is derived from the actual body and reachable accumulator sizes;
no whole-loop efficiency premise is supplied. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.AttachCompiler

open AGM

universe v w

private def foldWith {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (body : Expr CryptoOp ([key, attachState key, scalar, .list key, .list scalar] ++ Γ) (attachState key)) :
    Expr CryptoOp ([scalar, .list key, .list scalar] ++ Γ) (attachState key) :=
  .fold (.var (.there .here)) (.pair (.nat 0) .nil) body

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

include sizes lists mono

private theorem foldWith_time_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (body : Expr CryptoOp ([key, attachState key, scalar, .list key, .list scalar] ++ Γ) (attachState key))
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width workTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size rep.data.nat 0 ≤ width)
    (hi : Q.size (rep.env ([scalar, .list key, .list scalar] ++ Γ)) (default, keys, values, env) ≤ width)
    (ho : Q.size (rep.ty (attachState key))
      (keys.foldl (fun acc i => body.denote (arithmetic F G₁ G₂ K M cost)
        (i, acc, default, keys, values, env)) (0, [])) ≤ width)
    (hw : foldWork
      (fun i acc => body.denote (arithmetic F G₁ G₂ K M cost) (i, acc, default, keys, values, env))
      (fun i acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
        dataLaws primitiveBound body).time (i, acc, default, keys, values, env))
      (foldFee (Q := Q) overhead rep.data (rep.ty key) (rep.ty (attachState key))
        (rep.env ([scalar, .list key, .list scalar] ++ Γ)) (body.denote (arithmetic F G₁ G₂ K M cost))
        (default, keys, values, env)) keys (0, []) ≤ workTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (foldWith body)).time (default, keys, values, env) ≤
        workTime + 16 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty (.pair key scalar))
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [foldWith, attachState, tableTy, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.natBound, DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.foldBound,
    LanguageRepresentation.env, LanguageRepresentation.ty, List.cons_append, List.nil_append, List.append,
    Expr.denote, Var.get, id] at *
  grind only

omit sizes lists mono in
theorem body_denote {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (i : key.Value (cryptoBase F G₁ G₂ K M))
    (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((attachBody (indexTy := key)).weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost)
      (i, acc, default, keys, values, env) = attachStep default values acc i := by
  have h := (attachBody (indexTy := key)).weakenTail_denote (arithmetic F G₁ G₂ K M cost)
    (i, acc, default, keys, values, ()) env
  change ((attachBody (indexTy := key)).weakenTail Γ).denote _
    (i, acc, default, keys, values, env) = _ at h
  rw [h, ← Expr.run_value, attachBody_value]

theorem fold_time_bound {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
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
      primitiveBound ((attachFold (indexTy := key)).weakenTail Γ)).time (default, keys, values, env) ≤
        keyCap * (coeffCap * (comparisonTime + subtractTime +
          257 * overhead (128 * frameWidth width keyCap coeffCap)) + addTime +
          321 * overhead (128 * frameWidth width keyCap coeffCap)) +
            17 * overhead (128 * frameWidth width keyCap coeffCap) := by
  let W := frameWidth width keyCap coeffCap
  let fee := overhead (128 * W)
  let valid := fun i : key.Value (cryptoBase F G₁ G₂ K M) => Q.size (rep.ty key) i ≤ width
  let inv := Remaining (V := F) valid keyCap
  let step := fun i acc => ((attachBody (indexTy := key)).weakenTail Γ).denote
    (arithmetic F G₁ G₂ K M cost) (i, acc, default, keys, values, env)
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
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
  have hstep (i : key.Value (cryptoBase F G₁ G₂ K M)) (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F)) :
      step i acc = attachStep default values acc i := body_denote cost i acc default keys values env
  have hfold (xs : List (key.Value (cryptoBase F G₁ G₂ K M))) (hx : ∀ i ∈ xs, valid i)
      (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F)) (ha : inv xs.length acc) :
      inv 0 (xs.foldl (fun acc i => step i acc) acc) := by
    simp_rw [hstep]
    exact remaining_fold valid keyCap default values xs hx acc ha
  have hstate (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F))
      (remaining : Nat) (ha : inv remaining acc) :
      Q.size (rep.ty (attachState key)) acc ≤ (4 * keyCap + 3) * width := by
    exact state_encoded_size rep sizes lists acc width keyCap hh hf
      (hn acc.1 (by have := ha.1; omega)) ha.2.2 (by have := ha.2.1; omega)
  have hwork := foldWork_bound_remaining step
    (fun i acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound ((attachBody (indexTy := key)).weakenTail Γ)).time
        (i, acc, default, keys, values, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty key) (rep.ty (attachState key))
      (rep.env ([scalar, .list key, .list scalar] ++ Γ))
      (((attachBody (indexTy := key)).weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost))
      (default, keys, values, env))
    valid inv (coeffCap * (comparisonTime + subtractTime + 257 * fee) + addTime + 320 * fee)
    fee keyCap
    (by
      intro remaining hr i hi acc ha
      have hframe := body_frame_size rep sizes lists i acc default keys values env width keyCap coeffCap
        hh hf (hn acc.1 (by have := ha.1; omega)) hi ha.2.2
        (by have := ha.2.1; omega) hk hkc hvc he
      refine ⟨body_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        i acc default keys values env W comparisonTime subtractTime addTime coeffCap
        (hh.trans hw) (hu.trans hw) hframe (fun b => (hb b).trans hw)
        (fun n hn' => (hn n (by have := ha.1; omega)).trans hw)
        (fun f => (hf f).trans hw) hvc ?_
        (fun n hn' => hEq n (by have := ha.1; omega))
        (fun n hn' => hSub n (by have := ha.1; omega))
        (hAdd acc.1 (by have := ha.1; omega)), ?_⟩
      · intro xs hlen _
        have hs := lists.size_le_cap (rep.ty scalar) xs width coeffCap (fun f _ => hf f) hlen
        dsimp only [LanguageRepresentation.ty] at hs ⊢
        dsimp only [W, frameWidth]
        nlinarith
      · rw [hstep]
        exact remaining_step valid keyCap remaining default values i hi acc ha)
    (by
      intro xs hlen hxs acc ha
      have hs := lists.size_le_cap (rep.ty key) xs width keyCap hxs hlen
      have haSize := hstate acc xs.length ha
      have hout := hfold xs hxs acc ha
      have hoSize := hstate _ 0 hout
      unfold foldFee
      apply mono
      change _ ≤ 128 * W
      dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, attachState, tableTy,
        List.cons_append, List.nil_append, List.append, step, W, frameWidth] at *
      clear hn hf hEq hSub hAdd hstep hfold hstate
      grind only)
    keys hkc hk (0, []) ⟨by simpa, by simpa, by simp⟩
  have hout := hfold keys hk (0, []) ⟨by simpa, by simpa, by simp⟩
  have ho := hstate _ 0 hout
  have houtSize : Q.size (rep.ty (attachState key))
      (keys.foldl (fun acc i => step i acc) (0, [])) ≤ W := by
    dsimp only [W, frameWidth]
    nlinarith
  have hcap := Nat.mul_le_mul_right
    (coeffCap * (comparisonTime + subtractTime + 257 * fee) + addTime + 321 * fee) hkc
  have h := foldWith_time_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    ((attachBody (indexTy := key)).weakenTail Γ) default keys values env W
    (keys.length * (coeffCap * (comparisonTime + subtractTime + 257 * fee) + addTime + 321 * fee) + fee)
    (hh.trans hw) (hu.trans hw) ((hn 0 (by omega)).trans hw) henv houtSize
    (hwork.trans (by ring_nf; exact le_rfl))
  change (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound ((attachFold (indexTy := key)).weakenTail Γ)).time (default, keys, values, env) ≤ _ at h
  exact h.trans (by dsimp only [fee, W] at *; omega)

end Signatures.Runtime.BackendProgram.AttachCompiler
