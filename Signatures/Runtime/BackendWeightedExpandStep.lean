import Signatures.Runtime.BackendWeightedScale

/-! Cost composition for one signing-coefficient expansion step. The caller of
the generic composition lemma supplies the term-generator bound; scheme-specific
generator proofs discharge that obligation. Scaling and all retained-frame routing
are derived here from the actual expression, not supplied as whole-step budgets. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms BackendProgram

private def expandWith {indexTy messageTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (generate : Expr CryptoOp (messageTy :: rowTy messageTy :: .list (termTy indexTy) :: Γ)
      (.list (termTy indexTy)))
    (scaling : Expr CryptoOp ([.list (termTy indexTy), scalar, .list (termTy indexTy),
      .list (termTy indexTy), messageTy, rowTy messageTy, .list (termTy indexTy)] ++ Γ)
      (.list (termTy indexTy))) :
    Expr CryptoOp (rowTy messageTy :: .list (termTy indexTy) :: Γ) (.list (termTy indexTy)) :=
  .letE (.fst (.fst (.var .here)))
    (.letE generate
      (.letE (.var (.there (.there (.there .here))))
        (.letE (.snd (.var (.there (.there (.there .here)))))
          (.letE (.var (.there (.there .here))) scaling))))

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

private theorem expandWith_time {indexTy messageTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (generate : Expr CryptoOp (messageTy :: rowTy messageTy :: .list (termTy indexTy) :: Γ)
      (.list (termTy indexTy)))
    (scaling : Expr CryptoOp ([.list (termTy indexTy), scalar, .list (termTy indexTy),
      .list (termTy indexTy), messageTy, rowTy messageTy, .list (termTy indexTy)] ++ Γ)
      (.list (termTy indexTy)))
    (row : (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)
    (acc generated : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width termTime scalingTime : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env (rowTy messageTy :: .list (termTy indexTy) :: Γ)) (row, acc, env) ≤ width)
    (hv : generate.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, row, acc, env) = generated)
    (hg : Q.size (rep.ty (.list (termTy indexTy))) generated ≤ width)
    (ho : Q.size (rep.ty (.list (termTy indexTy)))
      (scaling.denote (arithmetic F G₁ G₂ K M cost)
        (generated, row.2, acc, generated, row.1.1, row, acc, env)) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound generate).time (row.1.1, row, acc, env) ≤ termTime)
    (hs : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scaling).time (generated, row.2, acc, generated, row.1.1, row, acc, env) ≤ scalingTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (expandWith generate scaling)).time (row, acc, env) ≤
        termTime + scalingTime + 128 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [expandWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
    List.cons_append, List.nil_append, List.append] at *
  simp only [hv] at *
  grind only

def expandStepWidth (width termCap accumulatorCap : Nat) : Nat :=
  (4 * termCap + 8 * accumulatorCap + 32) * width

def expandStepTime (overhead : Nat → Nat) (width termCap accumulatorCap termTime mulTime : Nat) : Nat :=
  let W := expandStepWidth width termCap accumulatorCap
  termTime + scaleTime overhead W termCap accumulatorCap mulTime + 128 * overhead (128 * W)

include lists in
/-- Compose term generation with actual native scaling and routing. Only the
generator's local bound is a premise; complete scheme bounds must derive it. -/
theorem expandStep_time {indexTy messageTy : Ty CryptoAtom}
    (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    (row : (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)
    (acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width termCap accumulatorCap termTime mulTime : Nat)
    (hh : header ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hr : Q.size (rep.ty (rowTy messageTy)) row ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ t ∈ terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ()),
      Q.size (rep.ty (termTy indexTy)) t ≤ width)
    (ha : ∀ t ∈ acc, Q.size (rep.ty (termTy indexTy)) t ≤ 3 * width)
    (htc : (terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ())).length ≤ termCap)
    (hac : acc.length ≤ accumulatorCap)
    (hgen : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (terms.weakenTail (rowTy messageTy :: .list (termTy indexTy) :: Γ))).time
        (row.1.1, row, acc, env) ≤ termTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (expandStep terms)).time (row, acc, env) ≤
        expandStepTime overhead width termCap accumulatorCap termTime mulTime := by
  let ts := terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ())
  let W := expandStepWidth width termCap accumulatorCap
  have hw : width ≤ W := by dsimp [W, expandStepWidth]; nlinarith
  have hprod := @sizes.prod_le
  have hmSize := (sizes.fst_le (rep.ty messageTy) (rep.ty point₁) row.1).trans
    ((sizes.fst_le (rep.ty (AGM.tokenTy messageTy)) (rep.ty scalar) row).trans hr)
  have hts := lists.size_le_cap (rep.ty (termTy indexTy)) ts width termCap ht htc
  have hacc := lists.size_le_cap (rep.ty (termTy indexTy)) acc (3 * width) accumulatorCap ha hac
  have htsSize : Q.size (rep.ty (.list (termTy indexTy))) ts ≤ (2 * termCap + 1) * width := by
    change Q.size (rep.ty (.list (termTy indexTy))) ts ≤ _ at hts
    nlinarith [Nat.mul_le_mul_left termCap hh]
  have haccSize : Q.size (rep.ty (.list (termTy indexTy))) acc ≤ (4 * accumulatorCap + 1) * width := by
    change Q.size (rep.ty (.list (termTy indexTy))) acc ≤ _ at hacc
    nlinarith [Nat.mul_le_mul_left accumulatorCap hh]
  have htail : Q.size (rep.env
      ([.list (termTy indexTy), messageTy, rowTy messageTy, .list (termTy indexTy)] ++ Γ))
      (ts, row.1.1, row, acc, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, List.cons_append,
      List.nil_append, List.append, W, expandStepWidth] at *
    grind only
  have hroot : Q.size (rep.env (rowTy messageTy :: .list (termTy indexTy) :: Γ))
      (row, acc, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, expandStepWidth] at *
    grind only
  have hscaled : ∀ t ∈ (ts.map fun t => (t.1, row.2 * t.2)).reverse ++ acc,
      Q.size (rep.ty (termTy indexTy)) t ≤ 3 * width := by
    intro t hit
    rcases List.mem_append.mp hit with hit | hit
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hit)
      have hi := (sizes.fst_le (rep.ty indexTy) (rep.ty scalar) u).trans (ht u hu)
      have hs := hf (row.2 * u.2)
      have hp := sizes.prod_le (rep.ty indexTy) (rep.ty scalar) (u.1, row.2 * u.2)
      dsimp only at hp
      exact hp.trans (by omega)
    · exact ha t hit
  have hout := lists.size_le_cap (rep.ty (termTy indexTy))
    ((ts.map fun t => (t.1, row.2 * t.2)).reverse ++ acc) (3 * width)
    (accumulatorCap + termCap) hscaled (by
      simp only [List.length_append, List.length_reverse, List.length_map]
      dsimp only [ts]
      omega)
  have houtSize : Q.size (rep.ty (.list (termTy indexTy)))
      ((ts.map fun t => (t.1, row.2 * t.2)).reverse ++ acc) ≤ W := by
    change Q.size (rep.ty (.list (termTy indexTy))) _ ≤ _ at hout
    dsimp only [W, expandStepWidth]
    nlinarith [Nat.mul_le_mul_left (accumulatorCap + termCap) hh]
  have hscale := scalePrepend_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    ts acc row.2 (Γ := [.list (termTy indexTy), messageTy, rowTy messageTy, .list (termTy indexTy)] ++ Γ)
    (ts, row.1.1, row, acc, env) W termCap accumulatorCap mulTime (hh.trans hw) htail
    (fun f => (hf f).trans hw) (fun t hit => (ht t hit).trans hw)
    (fun t hit => (ha t hit).trans (Nat.mul_le_mul_left 3 hw)) htc hac hm
  have hvalue := terms.weakenTail_denote (Δ := rowTy messageTy :: .list (termTy indexTy) :: Γ)
    (arithmetic F G₁ G₂ K M cost)
    (row.1.1, ()) (row, acc, env)
  have htime := expandWith_time rep data cost primitive laws dataLaws primitiveBound sizes mono
    (terms.weakenTail (rowTy messageTy :: .list (termTy indexTy) :: Γ)) scalePrepend
    row acc ts env W termTime (scaleTime overhead W termCap accumulatorCap mulTime)
    (hh.trans hw) hroot hvalue (htsSize.trans (by dsimp [W, expandStepWidth]; nlinarith))
    (by rw [scalePrepend_denote]; exact houtSize) hgen hscale
  exact htime

end Signatures.Runtime.WeightedAGM.Coefficients
