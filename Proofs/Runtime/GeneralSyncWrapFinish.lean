import Proofs.Runtime.GeneralSyncWrapSource
import Proofs.Runtime.Index
import Proofs.Runtime.Sampling
import Proofs.Runtime.Weakening
import Proofs.Runtime.Arithmetic

/-! # First-order code for the wrapper's finishing step

The finish re-expresses the forgery's hash coefficients over the recorded marks: one fold walks
the marks, looking up the attacker's next hash coefficient for a hash mark and the next signing
coefficient times the recorded correction for a signing mark, with the running counts kept in the
accumulator; a second fold appends the negated final scalar. Both are ordinary expressions of the
arithmetic language, so the backend charges every lookup, comparison and allocation. The
expressions are generic in a retained tail environment, so no weakening is needed to place them
inside the finish. -/

namespace Signatures.Runtime.SyncWrapGeneral

open Model.LazyAGM (tokenCoeff)

/-- The fold accumulator: coefficients so far (newest first), hashes seen, signatures seen. -/
abbrev accTy : Ty CryptoAtom := .pair (.list scalar) (.pair .nat .nat)

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
private abbrev v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))

/-- The fold body's environment: mark, accumulator, marks, hash coefficients, signing
coefficients, then the retained tail. -/
abbrev bodyEnv (Γ : List (Ty CryptoAtom)) : List (Ty CryptoAtom) :=
  [markTy, accTy, .list markTy, .list scalar, .list scalar] ++ Γ

/-- The remap environment: marks, hash coefficients, signing coefficients, then the tail. -/
abbrev remapEnv (Γ : List (Ty CryptoAtom)) : List (Ty CryptoAtom) :=
  [.list markTy, .list scalar, .list scalar] ++ Γ

variable {Γ : List (Ty CryptoAtom)}

/-- The signing coefficient at the current signing count. -/
def lookupSign : Expr CryptoOp (bodyEnv Γ) scalar :=
  .letE v4 (.letE (.op .zero .unit) (.letE (.snd (.snd v3))
    ((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail (bodyEnv Γ))))

/-- The hash coefficient at the current hash count. -/
def lookupHash : Expr CryptoOp (bodyEnv Γ) scalar :=
  .letE v3 (.letE (.op .zero .unit) (.letE (.fst (.snd v3))
    ((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail (bodyEnv Γ))))

/-- One mark: a signing mark contributes `ξ_j · c` and advances `j`, a hash mark contributes
`γ_i` and advances `i`. -/
def remapBody : Expr CryptoOp (bodyEnv Γ) accTy :=
  .branch (.fst v0)
    (.pair (.cons (.op .mul (.pair lookupSign (.snd v0))) (.fst v1))
      (.pair (.fst (.snd v1)) (.op .natAdd (.pair (.snd (.snd v1)) (.nat 1)))))
    (.pair (.cons lookupHash (.fst v1))
      (.pair (.op .natAdd (.pair (.fst (.snd v1)) (.nat 1))) (.snd (.snd v1))))

/-- The fold over the marks. -/
def remapFold : Expr CryptoOp (remapEnv Γ) accTy :=
  .fold v0 (.pair .nil (.pair (.nat 0) (.nat 0))) remapBody

/-- Coefficients over the marks in order: fold, then restore the order. -/
def remapExpr : Expr CryptoOp (remapEnv Γ) (.list scalar) :=
  .letE remapFold (.letE (.fst v0) reverseList)

/-- Append the negated final scalar to the coefficient list (`v0` the list, `v3` the scalar). -/
def appendOne : Expr CryptoOp [.list scalar, OutTy, .list markTy, scalar] (.list scalar) :=
  .fold (.letE v0 reverseList) (.cons (.op .neg v3) .nil) (.cons v0 v1)

/-- The coefficient list of the finished output. -/
def coeffsExpr : Expr CryptoOp [OutTy, .list markTy, scalar] (.list scalar) :=
  .letE (.snd (.snd (.snd v0)))
    (.letE (.fst (.snd (.snd v1)))
      (.letE (.letE v3 reverseList) (remapExpr (Γ := [OutTy, .list markTy, scalar]))))

/-- The finished output from the attacker's output, the marks and the final scalar. -/
def finExpr : Expr CryptoOp [OutTy, .list markTy, scalar] OutTy :=
  .letE coeffsExpr
    (.pair (.fst v1) (.pair (.fst (.snd v1)) (.pair appendOne (.snd (.snd (.snd v1))))))

/-! ## Semantics -/

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)

/-- The fold step on accumulators `(coefficients, hashes, signatures)`. -/
def remapStep (γ ξ : List F) (acc : List F × Nat × Nat) (m : Bool × F) : List F × Nat × Nat :=
  if m.1 = true then (tokenCoeff ξ acc.2.2 * m.2 :: acc.1, acc.2.1, acc.2.2 + 1)
  else (tokenCoeff γ acc.2.1 :: acc.1, acc.2.1 + 1, acc.2.2)

theorem lookupSign_denote (m : Bool × F) (acc : List F × Nat × Nat) (marks : List (Bool × F)) (γ ξ : List F)
    (tail : Env (cryptoBase F G₁ G₂ K M) Γ) :
    lookupSign.denote (arithmetic F G₁ G₂ K M cost) (m, acc, marks, γ, ξ, tail) = tokenCoeff ξ acc.2.2 := by
  have h := (index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail_denote
    (Δ := bodyEnv Γ) (arithmetic F G₁ G₂ K M cost) (acc.2.2, 0, ξ, ()) (m, acc, marks, γ, ξ, tail)
  simp only [lookupSign, Expr.denote, Var.get, arithmetic]
  change (((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail (bodyEnv Γ)).denote
    (arithmetic F G₁ G₂ K M cost) (Env.append (acc.2.2, 0, ξ, ()) (m, acc, marks, γ, ξ, tail))) = _
  rw [h, index_denote (arithmetic F G₁ G₂ K M cost) CryptoOp.natEq CryptoOp.natSub (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

theorem lookupHash_denote (m : Bool × F) (acc : List F × Nat × Nat) (marks : List (Bool × F)) (γ ξ : List F)
    (tail : Env (cryptoBase F G₁ G₂ K M) Γ) :
    lookupHash.denote (arithmetic F G₁ G₂ K M cost) (m, acc, marks, γ, ξ, tail) = tokenCoeff γ acc.2.1 := by
  have h := (index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail_denote
    (Δ := bodyEnv Γ) (arithmetic F G₁ G₂ K M cost) (acc.2.1, 0, γ, ()) (m, acc, marks, γ, ξ, tail)
  simp only [lookupHash, Expr.denote, Var.get, arithmetic]
  change (((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail (bodyEnv Γ)).denote
    (arithmetic F G₁ G₂ K M cost) (Env.append (acc.2.1, 0, γ, ()) (m, acc, marks, γ, ξ, tail))) = _
  rw [h, index_denote (arithmetic F G₁ G₂ K M cost) CryptoOp.natEq CryptoOp.natSub (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

theorem remapBody_denote (m : Bool × F) (acc : List F × Nat × Nat) (marks : List (Bool × F)) (γ ξ : List F)
    (tail : Env (cryptoBase F G₁ G₂ K M) Γ) :
    remapBody.denote (arithmetic F G₁ G₂ K M cost) (m, acc, marks, γ, ξ, tail) = remapStep γ ξ acc m := by
  have hs := lookupSign_denote (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost m acc marks γ ξ tail
  have hh := lookupHash_denote (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost m acc marks γ ξ tail
  by_cases hm : m.1 = true <;>
    simp only [remapBody, Expr.denote, Var.get, hs, hh, remapStep, hm, ite_true, ite_false, Bool.false_eq_true] <;>
    rfl

omit [DecidableEq F] in
theorem remapStep_fold (γ ξ : List F) (marks : List (Bool × F)) (out : List F) (i j : Nat) :
    (marks.foldl (remapStep γ ξ) (out, i, j)).1 = (remapMarks γ ξ marks i j).reverse ++ out := by
  induction marks generalizing out i j with
  | nil => rfl
  | cons m rest ih =>
    obtain ⟨flag, c⟩ := m
    cases flag <;> simp [List.foldl_cons, remapStep, remapMarks, ih]

theorem remapFold_denote (marks : List (Bool × F)) (γ ξ : List F) (tail : Env (cryptoBase F G₁ G₂ K M) Γ) :
    remapFold.denote (arithmetic F G₁ G₂ K M cost) (marks, γ, ξ, tail) = marks.foldl (remapStep γ ξ) ([], 0, 0) := by
  simp only [remapFold, Expr.denote, Var.get]
  have hstep : (fun acc m => remapBody.denote (arithmetic F G₁ G₂ K M cost) (m, acc, marks, γ, ξ, tail)) =
      remapStep γ ξ := by
    funext acc m
    exact remapBody_denote cost m acc marks γ ξ tail
  rw [hstep]

theorem remapExpr_denote (marks : List (Bool × F)) (γ ξ : List F) (tail : Env (cryptoBase F G₁ G₂ K M) Γ) :
    remapExpr.denote (arithmetic F G₁ G₂ K M cost) (marks, γ, ξ, tail) = remapMarks γ ξ marks 0 0 := by
  simp only [remapExpr, Expr.denote, Var.get]
  rw [reverseList_denote, remapFold_denote, remapStep_fold]
  simp

theorem foldl_cons_reverse {α : Type} (xs acc : List α) :
    xs.reverse.foldl (fun acc x => x :: acc) acc = xs ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [List.foldl_append, ih]

theorem appendOne_denote (coeffs : List F) (r : OutTy.Value (cryptoBase F G₁ G₂ K M)) (marks : List (Bool × F)) (v : F) :
    appendOne.denote (arithmetic F G₁ G₂ K M cost) (coeffs, r, marks, v, ()) = coeffs ++ [-v] := by
  simp only [appendOne, Expr.denote, Var.get, arithmetic]
  rw [reverseList_denote, foldl_cons_reverse]

theorem coeffsExpr_denote (r : OutTy.Value (cryptoBase F G₁ G₂ K M)) (marks : List (Bool × F)) (v : F) :
    coeffsExpr.denote (arithmetic F G₁ G₂ K M cost) (r, marks, v, ()) =
      remapMarks r.2.2.1 r.2.2.2 marks.reverse 0 0 := by
  simp only [coeffsExpr, Expr.denote, Var.get]
  rw [reverseList_denote, remapExpr_denote]

theorem finExpr_denote (r : OutTy.Value (cryptoBase F G₁ G₂ K M)) (marks : List (Bool × F)) (v : F) :
    finExpr.denote (arithmetic F G₁ G₂ K M cost) (r, marks, v, ()) =
      (r.1, (r.2.1, (remapMarks r.2.2.1 r.2.2.2 marks.reverse 0 0 ++ [-v], r.2.2.2))) := by
  simp only [finExpr, Expr.denote, Var.get]
  rw [coeffsExpr_denote, appendOne_denote]

/-- The compiled finish computes `fin`. -/
theorem finExpr_denote_fin (finalFn : K × F → F) (r : OutTy.Value (cryptoBase F G₁ G₂ K M)) (marks : List (Bool × F)) :
    finExpr.denote (arithmetic F G₁ G₂ K M cost) (r, marks, finalFn r.1, ()) = fin (G₁ := G₁) (G₂ := G₂) (M := M) finalFn r marks :=
  finExpr_denote cost r marks (finalFn r.1)

end Signatures.Runtime.SyncWrapGeneral
