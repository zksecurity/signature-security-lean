import Signatures.Runtime.BackendSchnorrROMSelectionLocalCost

/-! Derive the complete selection of one returned pass from its existing
encoding invariant and individual primitive contracts. No selector budget is assumed. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

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

structure Operations (width liveCap qH scaleTime addTime messageTime pointTime incrementTime comparisonTime : Nat) : Prop where
  scale : ∀ z g, Q.size (rep.ty scalar) z ≤ 3 * width → Q.size (rep.ty point₁) g ≤ 3 * width →
    Q.size (rep.ty point₁) (z • g) ≤ 3 * width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime
  add : ∀ g h, Q.size (rep.ty point₁) g ≤ 3 * width → Q.size (rep.ty point₁) h ≤ 3 * width →
    Q.size (rep.ty point₁) (g + h) ≤ 3 * width ∧ (primitiveBound .add₁).time (g, h) ≤ addTime
  point : ∀ g h, Q.size (rep.ty point₁) g ≤ 3 * width → Q.size (rep.ty point₁) h ≤ 3 * width →
    (primitiveBound .point₁Eq).time (g, h) ≤ pointTime
  message : ∀ m n, Q.size (rep.ty message) m ≤ 3 * width → Q.size (rep.ty message) n ≤ 3 * width →
    (primitiveBound .messageEq).time (m, n) ≤ messageTime
  increment : ∀ n ≤ liveCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime
  compare : ∀ n ≤ liveCap, (primitiveBound .natLt).time (n, qH + 1) ≤ comparisonTime

include sizes in
omit [Q.HasCategory] QP QS [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁]
  [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem choice_size (width cap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hn : ∀ n ≤ cap, Q.size rep.data.nat n ≤ width)
    (result : Bool × Nat) (hr : result.2 ≤ cap) : Q.size (rep.ty indexResult) result ≤ 3 * width := by
  have hp := sizes.prod_le rep.data.bool rep.data.nat result
  have hbool := hb result.1
  have hnat := hn result.2 hr
  change Q.size (rep.ty indexResult) result ≤ _ at hp
  omega

omit [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₂] [DecidableEq K] in
theorem oneValue_index_le (qH : Nat) (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
    (oneValue qH p).2 ≤ qH := by
  simpa only [value, List.foldl_cons, List.foldl_nil] using value_index_le qH [p]

def oneTime (overhead : Nat → Nat) (frame liveCap scaleTime addTime messageTime pointTime incrementTime comparisonTime : Nat) : Nat :=
  indexTime overhead frame liveCap messageTime pointTime incrementTime +
    2 * scaleTime + addTime + pointTime + comparisonTime + 1024 * overhead (512 * frame)

include sizes lists mono

theorem oneExpression_time {Γ : List (Ty CryptoAtom)}
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width frame managedCap liveCap qH scaleTime addTime messageTime pointTime incrementTime comparisonTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ max liveCap qH + 1, Q.size rep.data.nat n ≤ width)
    (hw : 8 * width ≤ frame)
    (hi : Q.size (rep.env (cachePassOutput :: Γ)) (p, env) ≤ frame)
    (bound : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap p)
    (ops : Operations rep cost primitive primitiveBound width liveCap qH
      scaleTime addTime messageTime pointTime incrementTime comparisonTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (oneExpression (Γ := Γ) qH)).time (p, env) ≤
      oneTime overhead frame liveCap scaleTime addTime messageTime pointTime incrementTime comparisonTime := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfields : Q.size (rep.ty message) p.1.1.1 ≤ width ∧
      Q.size (rep.ty point₁) p.1.1.2.1 ≤ width ∧ Q.size (rep.ty scalar) p.1.1.2.2 ≤ width := by
    have hf := bound.forged
    simp only [LanguageRepresentation.ty] at *
    grind only
  have hg := bound.caches.config.1
  have hpk := bound.caches.config.2
  have hc := bound.challenge
  have hz := ops.scale p.1.1.2.2 p.2.1.1 (by have := hfields.2.2; omega) (by omega)
  have hchallenge := ops.scale p.1.2 p.2.1.2 hc (by omega)
  have hadd := ops.add p.1.1.2.1 (p.1.2 • p.2.1.2) (by have := hfields.2.1; omega) hchallenge.1
  have heq := ops.point (p.1.1.2.2 • p.2.1.1) (p.1.1.2.1 + p.1.2 • p.2.1.2) hz.1 hadd.1
  have hv := verifyExpression_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    p env frame scaleTime addTime pointTime (by omega) (fun b => (hb b).trans (by omega)) hi
    (hz.1.trans (by omega)) (hchallenge.1.trans (by omega)) (hadd.1.trans (by omega)) hz.2 hchallenge.2 hadd.2 heq
  have hk : Q.size (rep.ty hashKey) (p.1.1.1, p.1.1.2.1) ≤ frame := by
    have hp := sizes.prod_le (rep.ty message) (rep.ty point₁) (p.1.1.1, p.1.1.2.1)
    change Q.size (rep.ty hashKey) _ ≤ _ at hp
    dsimp only at hp
    have hm := hfields.1
    have hr := hfields.2.1
    omega
  have hcell : ∀ x ∈ p.2.2.2, Q.size (rep.ty (.pair hashKey scalar)) x ≤ frame := by
    intro x hx
    obtain ⟨hk, hf⟩ := bound.caches.live.1 x hx
    have hp := sizes.prod_le (rep.ty hashKey) (rep.ty scalar) x
    change Q.size (rep.ty (.pair hashKey scalar)) x ≤ _ at hp
    omega
  have hmessage : ∀ x ∈ p.2.2.2, (primitiveBound .messageEq).time (x.1.1, p.1.1.1) ≤ messageTime := by
    intro x hx
    apply ops.message
    · have hk := (bound.caches.live.1 x hx).1
      exact (sizes.fst_le (rep.ty message) (rep.ty point₁) x.1).trans hk
    · have := hfields.1; omega
  have hpoint : ∀ x ∈ p.2.2.2, (primitiveBound .point₁Eq).time (x.1.2, p.1.1.2.1) ≤ pointTime := by
    intro x hx
    apply ops.point
    · have hk := (bound.caches.live.1 x hx).1
      exact (sizes.snd_le (rep.ty message) (rep.ty point₁) x.1).trans hk
    · have := hfields.2.1; omega
  have hsearch := liveIndex_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    (Γ := cachePassOutput :: Γ) (p.1.1.1, p.1.1.2.1) p.2.2.2 (p, env)
    frame liveCap messageTime pointTime incrementTime (by omega) (by omega)
    (fun b => (hb b).trans (by omega)) (fun n hl => (hn n (by omega)).trans (by omega))
    hk hi hcell bound.caches.live.2 hmessage hpoint ops.increment
  have hcount : ((indexExpression (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) (p, env)).2 ≤ liveCap := by
    rw [indexExpression_denote]
    have h := List.findIdx_le_length (xs := p.2.2.2.reverse)
      (p := fun x => decide (x.1 = (p.1.1.1, p.1.1.2.1)))
    have hl := bound.caches.live.2
    simpa only [List.length_reverse] using h.trans (by simpa using hl)
  have hindexSize := choice_size rep sizes width liveCap hh hb (fun n hl => hn n (by omega)) _ hcount
  have hindex := indexExpressionWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (liveIndex.weakenTail (cachePassOutput :: Γ)) p env frame
    (indexTime overhead frame liveCap messageTime pointTime incrementTime) (by omega) hi
    (hindexSize.trans (by omega)) hsearch
  have hguardSize : Q.size (rep.ty indexResult)
      ((guardExpression (Γ := cachePassOutput :: Γ) qH).denote (arithmetic F G₁ G₂ K M cost)
        ((indexExpression (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) (p, env), p, env)) ≤ frame := by
    rw [guardExpression_denote]
    unfold guarded
    split
    · exact hindexSize.trans (by omega)
    · exact (choice_size rep sizes width 0 hh hb (fun n hl => hn n (by omega)) (false, 0) (by simp)).trans (by omega)
  have hguardRoot : Q.size (rep.env (indexResult :: cachePassOutput :: Γ))
      ((indexExpression (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) (p, env), p, env) ≤ 2 * frame := by
    have hp := sizes.prod_le (rep.ty indexResult) (rep.env (cachePassOutput :: Γ))
      ((indexExpression (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) (p, env), p, env)
    change Q.size (rep.env (indexResult :: cachePassOutput :: Γ)) _ ≤ _ at hp
    dsimp only at hp
    omega
  have hguard := guardExpression_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (Γ := cachePassOutput :: Γ)
    qH ((indexExpression (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) (p, env)) (p, env)
    (2 * frame) comparisonTime (by omega) (by omega) (fun b => (hb b).trans (by omega))
    ((hn 0 (by omega)).trans (by omega)) ((hn (qH + 1) (by omega)).trans (by omega))
    hguardRoot (ops.compare _ hcount)
  have ht := oneExpressionWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    verifyExpression indexExpression (guardExpression qH) p env frame
    (2 * scaleTime + addTime + pointTime + 512 * overhead (256 * frame))
    (indexTime overhead frame liveCap messageTime pointTime incrementTime + 128 * overhead (128 * frame))
    (comparisonTime + 128 * overhead (128 * (2 * frame)))
    (by omega) (by omega) (fun b => (hb b).trans (by omega)) ((hn 0 (by omega)).trans (by omega))
    hi (hindexSize.trans (by omega)) hguardSize hv hindex hguard
  have hfee₁ := mono (show 256 * frame ≤ 512 * frame by omega)
  have hfee₂ := mono (show 128 * frame ≤ 512 * frame by omega)
  have hfee₃ := mono (show 128 * (2 * frame) ≤ 512 * frame by omega)
  change (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    (oneExpressionWith verifyExpression indexExpression (guardExpression qH))).time (p, env) ≤ _
  unfold oneTime
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeSelection
