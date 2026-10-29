import Proofs.Runtime.WeightedTerms
import Proofs.Runtime.TokenCoefficients
import Proofs.LinearFunctional.Spec.LazyAGMReduction

/-! Executable expansion of chronological signing coefficients into weighted
base terms. Each reply occurrence keeps its own coefficient. Zero coefficients
still produce terms, missing coefficients are zero, and surplus coefficients
produce no reply. Two cons folds and a final reversal preserve source order;
no base-index or message domain is enumerated. -/

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

abbrev rowTy (messageTy : Ty CryptoAtom) : Ty CryptoAtom := .pair (AGM.tokenTy messageTy) scalar

variable {indexTy messageTy : Ty CryptoAtom}

/-- Prepend scaled terms in reverse order to the accumulated result. -/
def scalePrepend {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp ([.list (termTy indexTy), scalar, .list (termTy indexTy)] ++ Γ) (.list (termTy indexTy)) :=
  .fold v0 v2 (.cons (.pair (.fst v0) (.op .mul (.pair v3 (.snd v0)))) v1)

/-- Generate this signing reply's bases and multiply each by its coefficient. -/
def expandStep (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (rowTy messageTy :: .list (termTy indexTy) :: Γ) (.list (termTy indexTy)) :=
  .letE (.fst (.fst v0))
    (.letE (terms.weakenTail (rowTy messageTy :: .list (termTy indexTy) :: Γ))
      (.letE v3 (.letE (.snd v3) (.letE v2 scalePrepend))))

/-- Expand rows in chronological order, then restore the order of all terms. -/
def expandRows (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (.list (rowTy messageTy) :: Γ) (.list (termTy indexTy)) :=
  .letE (.fold v0 .nil (expandStep terms)) reverseList

/-- Convert the simulator's backwards log to chronological coefficient rows,
then expand each signed message into its source term list. -/
def signedTerms (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy))) :
    Expr CryptoOp [.list (AGM.tokenTy messageTy), .list scalar] (.list (termTy indexTy)) :=
  .letE AGM.tokenRows (expandRows terms)

private theorem scale_fold {I F : Type} [Mul F] (coeff : F)
    (terms : List (I × F)) (acc : List (I × F)) :
    terms.foldl (fun saved t => (t.1, coeff * t.2) :: saved) acc =
      (terms.map fun t => (t.1, coeff * t.2)).reverse ++ acc := by
  induction terms generalizing acc with
  | nil => simp
  | cons t terms ih => simp [ih, List.append_assoc]

private theorem expand_fold {I F M G : Type} [Mul F] (terms : M → List (I × F))
    (rows : List ((M × G) × F)) (acc : List (I × F)) :
    rows.foldl (fun saved row =>
      ((terms row.1.1).map fun t => (t.1, row.2 * t.2)).reverse ++ saved) acc =
      (rows.flatMap fun row => (terms row.1.1).map fun t => (t.1, row.2 * t.2)).reverse ++ acc := by
  induction rows generalizing acc with
  | nil => simp
  | cons row rows ih => simp [ih, List.append_assoc]

/-- Message and index representation changes commute with chronological source
expansion. No injectivity is needed for this list identity; cache transport
separately requires an injective index representation. -/
theorem source_signedTerms_map {F I J A B G : Type} [MulZeroOneClass F]
    (message : A → B) (encode : I → J) (terms : B → List (I × F))
    (coeff : List F) (tr : List (A × G)) :
    Model.LazyAGM.WeightedReduction.signedTerms
        (fun m => (terms (message m)).map (Prod.map encode id)) coeff tr =
      (Model.LazyAGM.WeightedReduction.signedTerms terms coeff
        (tr.map (Prod.map message id))).map (Prod.map encode id) := by
  simp only [Model.LazyAGM.WeightedReduction.signedTerms, List.mapIdx_eq_zipIdx_map,
    List.map_flatten, List.zipIdx_map, List.map_map, Function.comp_def,
    Prod.map, id_eq]


variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem scalePrepend_denote (terms : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (coeff : F) (acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    scalePrepend.denote (arithmetic F G₁ G₂ K M cost) (terms, coeff, acc, env) =
      (terms.map fun t => (t.1, coeff * t.2)).reverse ++ acc := by
  simpa only [scalePrepend, Expr.denote, v0, v1, v2, v3, Var.get, arithmetic] using
    scale_fold coeff terms acc

theorem expandStep_denote (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    (row : (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)
    (acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    (expandStep terms).denote (arithmetic F G₁ G₂ K M cost) (row, acc, env) =
      ((terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ())).map
        fun t => (t.1, row.2 * t.2)).reverse ++ acc := by
  have ht := terms.weakenTail_denote (Δ := rowTy messageTy :: .list (termTy indexTy) :: Γ)
    (arithmetic F G₁ G₂ K M cost) (row.1.1, ()) (row, acc, env)
  simp only [expandStep, Expr.denote, v0, v2, v3, Var.get]
  rw [show (terms.weakenTail (rowTy messageTy :: .list (termTy indexTy) :: Γ)).denote
      (arithmetic F G₁ G₂ K M cost) (row.1.1, row, acc, env) =
        terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ()) from ht]
  exact scalePrepend_denote cost _ _ _ _

theorem expandRows_denote (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    (rows : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    (expandRows terms).denote (arithmetic F G₁ G₂ K M cost) (rows, env) =
      rows.flatMap fun row =>
        (terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ())).map fun t => (t.1, row.2 * t.2) := by
  change (reverseList (Γ := .list (rowTy messageTy) :: Γ)).denote (arithmetic F G₁ G₂ K M cost)
    (rows.foldl (fun acc row => (expandStep terms (Γ := .list (rowTy messageTy) :: Γ)).denote (arithmetic F G₁ G₂ K M cost)
      (row, acc, rows, env)) [], rows, env) = _
  rw [reverseList_denote]
  have hstep :
      (fun acc row => (expandStep terms (Γ := .list (rowTy messageTy) :: Γ)).denote
        (arithmetic F G₁ G₂ K M cost) (row, acc, rows, env)) =
      (fun acc row => ((terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ())).map
        fun t => (t.1, row.2 * t.2)).reverse ++ acc) := by
    funext acc row
    exact expandStep_denote cost terms row acc (Γ := .list (rowTy messageTy) :: Γ) (rows, env)
  rw [hstep, expand_fold (fun m => terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())) rows []]
  simp

theorem signedTerms_denote (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    (tr : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    (signedTerms terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()) =
      Model.LazyAGM.WeightedReduction.signedTerms
        (fun m => terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())) coeff tr.reverse := by
  simp only [signedTerms, Expr.denote]
  rw [show AGM.tokenRows.denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()) =
      tr.reverse.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff coeff n)) from
        (Expr.run_value _ _ _).symm.trans (AGM.tokenRows_value cost tr coeff)]
  rw [expandRows_denote]
  simp only [Model.LazyAGM.WeightedReduction.signedTerms, List.flatMap,
    List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def]

/-- The OOPS expansion is exactly the source's weighted signing transcript. -/
theorem oops_signedTerms_denote (d : Nat) (tr : List ((F × K) × G₁)) (coeff : List F) :
    (signedTerms (Terms.oops d)).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()) =
      Model.LazyAGM.WeightedReduction.signedTerms (OOPS.LazyAGM.terms d) coeff tr.reverse := by
  rw [signedTerms_denote]
  have ht : (fun m => (Terms.oops d).denote (arithmetic F G₁ G₂ K M cost) (m, ())) =
      OOPS.LazyAGM.terms d := by
    funext m
    exact (Expr.run_value _ _ _).symm.trans (Terms.oops_value cost d m)
  rw [ht]

/-- The synchronized PS expansions are the source's weighted signing transcripts. -/
theorem sync_signedTerms_denote (weighted : Bool) (tr : List ((K × F) × G₁)) (coeff : List F) :
    (signedTerms (Terms.sync weighted)).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()) =
      Model.LazyAGM.WeightedReduction.signedTerms (Terms.syncTerms weighted) coeff tr.reverse := by
  rw [signedTerms_denote]
  have ht : (fun m => (Terms.sync weighted).denote (arithmetic F G₁ G₂ K M cost) (m, ())) =
      Terms.syncTerms weighted := by
    funext m
    exact (Expr.run_value _ _ _).symm.trans (Terms.sync_value cost weighted m)
  rw [ht]

/-- Proximity's tuple messages and finite coordinate tags preserve the original
source expansion, including the constant coordinate and every zero term. -/
theorem proximity_signedTerms_denote (ell : Nat)
    (tr : List ((Weights.proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M) × G₁))
    (coeff : List F) :
    (signedTerms (Terms.proximity ell)).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()) =
      (Model.LazyAGM.WeightedReduction.signedTerms Proximity.LazyAGM.terms coeff
        (tr.reverse.map (Prod.map (Weights.proximityMessageEquiv ell) id))).map
          (Prod.map Weights.encodeProximityKey id) := by
  rw [signedTerms_denote]
  have ht : (fun m => (Terms.proximity ell).denote (arithmetic F G₁ G₂ K M cost) (m, ())) =
      (fun m => (Proximity.LazyAGM.terms (Weights.proximityMessageEquiv ell m)).map
        (Prod.map Weights.encodeProximityKey id)) := by
    funext m
    exact (Expr.run_value _ _ _).symm.trans (Terms.proximity_value cost ell m)
  rw [ht]
  exact source_signedTerms_map (Weights.proximityMessageEquiv ell)
    Weights.encodeProximityKey Proximity.LazyAGM.terms coeff tr.reverse


end Signatures.Runtime.WeightedAGM.Coefficients
