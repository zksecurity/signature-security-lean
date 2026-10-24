import Proofs.Runtime.SchnorrAGMEncoding
import Proofs.Runtime.BackendAttachTable

/-! Native affine flattening over the chronological received basis. Positional
coefficient attachment uses the existing charged list implementation. Missing
coefficients are zero and surplus coefficients produce no basis entries. -/

open Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.Flatten

abbrev rowTy : Ty CryptoAtom := .pair affineTy scalar
abbrev rowsTy : Ty CryptoAtom := .list rowTy

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)

/-- Two field products and two additions per chronological basis entry. -/
def body {Γ : List (Ty CryptoAtom)} : Expr CryptoOp (rowTy :: affineTy :: Γ) affineTy :=
  .pair (.op .add (.pair (.fst v1) (.op .mul (.pair (.snd v0) (.fst (.fst v0))))))
    (.op .add (.pair (.snd v1) (.op .mul (.pair (.snd v0) (.snd (.fst v0))))))

def sumRows {Γ : List (Ty CryptoAtom)} : Expr CryptoOp (rowsTy :: scalar :: Γ) affineTy :=
  .fold v0 (.pair v1 v1) body

def expression {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp ([.list affineTy, .list scalar] ++ Γ) affineTy :=
  .letE (.op .zero .unit) (.letE ((AGM.attachTable (indexTy := affineTy)).weakenTail Γ) sumRows)

def total {F : Type} [Mul F] [AddMonoid F] (rows : List ((F × F) × F)) : F × F :=
  ((rows.map fun row => row.2 * row.1.1).sum, (rows.map fun row => row.2 * row.1.2).sum)

def value {F : Type} [Mul F] [AddMonoid F] (reps : List (F × F)) (coeff : List F) : F × F :=
  total (reps.mapIdx fun n a => (a, (coeff[n]?).getD 0))

private theorem fold_total {F : Type} [Semiring F] (rows : List ((F × F) × F)) (acc : F × F) :
    rows.foldl (fun acc row => (acc.1 + row.2 * row.1.1, acc.2 + row.2 * row.1.2)) acc =
      (acc.1 + (total rows).1, acc.2 + (total rows).2) := by
  induction rows generalizing acc with
  | nil => simp [total]
  | cons row rows ih => simp [ih, total, add_assoc]

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem body_denote {Γ : List (Ty CryptoAtom)} (row : (F × F) × F) (acc : F × F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    body.denote (arithmetic F G₁ G₂ K M cost) (row, acc, env) =
      (acc.1 + row.2 * row.1.1, acc.2 + row.2 * row.1.2) := rfl

theorem sumRows_denote {Γ : List (Ty CryptoAtom)} (rows : List ((F × F) × F)) (z : F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    sumRows.denote (arithmetic F G₁ G₂ K M cost) (rows, z, env) =
      (z + (total rows).1, z + (total rows).2) := by
  change rows.foldl (fun acc row => (acc.1 + row.2 * row.1.1, acc.2 + row.2 * row.1.2)) (z, z) = _
  exact fold_total rows (z, z)

theorem expression_denote {Γ : List (Ty CryptoAtom)} (reps : List (F × F)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    expression.denote (arithmetic F G₁ G₂ K M cost) (reps, coeff, env) = value reps coeff := by
  change (sumRows (Γ := [.list affineTy, .list scalar] ++ Γ)).denote (arithmetic F G₁ G₂ K M cost)
    (((AGM.attachTable (indexTy := affineTy)).weakenTail Γ).denote
      (arithmetic F G₁ G₂ K M cost) (0, reps, coeff, env), 0, reps, coeff, env) = _
  rw [BackendProgram.AttachCompiler.table_denote, sumRows_denote]
  simp only [zero_add, value]

omit [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem value_source (reps : List (Affine F)) (coeff : List F) :
    value (reps.map encodeAffine) coeff = encodeAffine (flatten coeff reps) := by
  simp only [value, total, flatten, combine, encodeAffine,
    List.mapIdx_eq_zipIdx_map, List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq]

/-- No algebraicity or equal-length premise is needed for the source convention. -/
theorem source {Γ : List (Ty CryptoAtom)} (reps : List (Affine F)) (coeff : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    expression.denote (arithmetic F G₁ G₂ K M cost) (reps.map encodeAffine, coeff, env) =
      encodeAffine (flatten coeff reps) := by
  rw [expression_denote, value_source]

end Signatures.Runtime.SchnorrAGM.Native.Flatten
