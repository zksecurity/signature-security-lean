import Proofs.Runtime.LazyAGMReply
import Proofs.Runtime.TokenCoefficients
import Proofs.Runtime.IndexedIteration
import Proofs.Runtime.Length

/-! First-order effectful evaluation of weighted terms. The index type is
independent of the signed-message type. The loop computes its length, scans to
each term, reads the private cache and updates a scalar or scalar-pair sum.
Ordering, repeated keys and zero-weight queries are preserved exactly. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.WeightedAGM.Evaluate

open LazyAGM.ReplySyntax

variable {indexTy : Ty CryptoAtom}

abbrev evalRowTy (indexTy : Ty CryptoAtom) : Ty CryptoAtom := .pair indexTy scalar
abbrev evalStateTy (value : Ty CryptoAtom) : Ty CryptoAtom := .pair .nat value

inductive EvalCmd (indexTy value : Ty CryptoAtom) : Ty CryptoAtom → Ty CryptoAtom → Type
  | lookup : EvalCmd indexTy value indexTy value

def selectRow {value : Ty CryptoAtom} :
    Expr CryptoOp [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)] (evalRowTy indexTy) :=
  .letE v1 (.letE v3 (.letE (.fst v2)
    ((index CryptoOp.natEq CryptoOp.natSub).weakenTail
      [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)])))

def evalUpdate {value : Ty CryptoAtom} (combine : Expr CryptoOp [value, scalar, value] value) :
    Expr CryptoOp [value, (evalRowTy indexTy), evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)] (evalStateTy value) :=
  .pair (.op .natAdd (.pair (.fst v2) (.nat 1)))
    (.letE (.snd v2) (.letE (.snd v2) (.letE v2
      (combine.weakenTail [value, (evalRowTy indexTy), evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]))))

def evalBody {value : Ty CryptoAtom} (combine : Expr CryptoOp [value, scalar, value] value) :
    Program CryptoOp (EvalCmd indexTy value) [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)] (evalStateTy value) :=
  .bind (.ret selectRow)
    (.bind (.query .lookup (.fst v0)) (.ret (evalUpdate combine)))

def evaluateRows {value : Ty CryptoAtom}
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Program CryptoOp (EvalCmd indexTy value) [.list (evalRowTy indexTy), (evalRowTy indexTy)] value :=
  .bind (.loop (listLength CryptoOp.natAdd) (.pair (.nat 0) zero) (evalBody combine)) (.ret (.snd v0))

def goodCombine : Expr CryptoOp [scalar, scalar, scalar] scalar :=
  .op .add (.pair v2 (.op .mul (.pair v1 v0)))

def badCombine : Expr CryptoOp [.pair scalar scalar, scalar, .pair scalar scalar] (.pair scalar scalar) :=
  .pair (.op .add (.pair (.fst v2) (.op .mul (.pair v1 (.fst v0)))))
    (.op .add (.pair (.snd v2) (.op .mul (.pair v1 (.snd v0)))))

def evaluateGood : Program CryptoOp (EvalCmd indexTy scalar) [.list (evalRowTy indexTy), (evalRowTy indexTy)] scalar :=
  evaluateRows (.op .zero .unit) goodCombine

def evaluateBad : Program CryptoOp (EvalCmd indexTy (.pair scalar scalar)) [.list (evalRowTy indexTy), (evalRowTy indexTy)] (.pair scalar scalar) :=
  evaluateRows (.pair (.op .zero .unit) (.op .zero .unit)) badCombine

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem selectRow_denote {value : Ty CryptoAtom}
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) :
    (selectRow (value := value)).denote (arithmetic F G₁ G₂ K M cost) ((n, acc), rows, default, ()) =
      (rows[n]?).getD default := by
  have h := (index (cell := (evalRowTy indexTy)) CryptoOp.natEq CryptoOp.natSub).weakenTail_denote
    (Δ := [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]) (arithmetic F G₁ G₂ K M cost)
    (n, default, rows, ()) ((n, acc), rows, default, ())
  simp only [selectRow, v1, v2, v3, Expr.denote, Var.get, Env.append] at h ⊢
  rw [h, index_denote _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)]

theorem evalUpdate_denote {value : Ty CryptoAtom}
    (combine : Expr CryptoOp [value, scalar, value] value)
    (answer : value.Value (cryptoBase F G₁ G₂ K M)) (row : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) :
    (evalUpdate combine).denote (arithmetic F G₁ G₂ K M cost) (answer, row, (n, acc), rows, default, ()) =
      (n + 1, combine.denote (arithmetic F G₁ G₂ K M cost) (answer, row.2, acc, ())) := by
  have h := combine.weakenTail_denote
    (Δ := [value, (evalRowTy indexTy), evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)])
    (arithmetic F G₁ G₂ K M cost) (answer, row.2, acc, ())
    (answer, row, (n, acc), rows, default, ())
  simp only [evalUpdate, v2, Expr.denote, Var.get, Env.append] at h ⊢
  rw [h]
  rfl

variable {N : Type → Type} [Monad N] [LawfulMonad N] {value : Ty CryptoAtom}

def evalSemantics (lookup : indexTy.Value (cryptoBase F G₁ G₂ K M) → N (value.Value (cryptoBase F G₁ G₂ K M))) :
    SemanticsM (cryptoBase F G₁ G₂ K M) (EvalCmd indexTy value) N := fun instr =>
  match instr with
  | .lookup => lookup

theorem evalBody_denote
    (lookup : indexTy.Value (cryptoBase F G₁ G₂ K M) → N (value.Value (cryptoBase F G₁ G₂ K M)))
    (combine : Expr CryptoOp [value, scalar, value] value)
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) :
    (evalBody combine).denote (arithmetic F G₁ G₂ K M cost) (evalSemantics lookup)
      ((n, acc), rows, default, ()) =
      indexedStep (fun row acc => do
        let answer ← lookup row.1
        pure (combine.denote (arithmetic F G₁ G₂ K M cost) (answer, row.2, acc, ()))) rows default (n, acc) := by
  simp only [evalBody, Program.denote, pure_bind]
  rw [selectRow_denote cost]
  simp only [evalSemantics, v0, Expr.denote, Var.get]
  simp_rw [evalUpdate_denote cost]
  simp only [indexedStep, bind_assoc, pure_bind]

theorem evaluateRows_denote
    (lookup : indexTy.Value (cryptoBase F G₁ G₂ K M) → N (value.Value (cryptoBase F G₁ G₂ K M)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) :
    (evaluateRows zero combine).denote (arithmetic F G₁ G₂ K M cost) (evalSemantics lookup) (rows, default, ()) =
      rows.foldlM (fun acc row => do
        let answer ← lookup row.1
        pure (combine.denote (arithmetic F G₁ G₂ K M cost) (answer, row.2, acc, ())))
          (zero.denote (arithmetic F G₁ G₂ K M cost) (rows, default, ())) := by
  have hbody : (fun acc => (evalBody combine).denote (arithmetic F G₁ G₂ K M cost)
      (evalSemantics lookup) (acc, rows, default, ())) =
      indexedStep (fun row acc => do
        let answer ← lookup row.1
        pure (combine.denote (arithmetic F G₁ G₂ K M cost) (answer, row.2, acc, ()))) rows default := by
    funext acc
    exact evalBody_denote cost lookup combine acc.1 acc.2 rows default
  have hlen := listLength_denote (cell := (evalRowTy indexTy)) (Γ := [(evalRowTy indexTy)])
    (arithmetic F G₁ G₂ K M cost) CryptoOp.natAdd (fun _ _ => rfl) rows (default, ())
  simp only [evaluateRows, Program.denote, hlen,
    Expr.denote, hbody, repeat_indexed, bind_map_left, v0, Var.get, bind_pure]

theorem goodCombine_denote (answer coeff acc : F) :
    goodCombine.denote (arithmetic F G₁ G₂ K M cost) (answer, coeff, acc, ()) = acc + coeff • answer := by
  simp [goodCombine, v0, v1, v2, Expr.denote, Var.get, arithmetic, smul_eq_mul]

theorem badCombine_denote (answer acc : F × F) (coeff : F) :
    badCombine.denote (arithmetic F G₁ G₂ K M cost) (answer, coeff, acc, ()) = acc + coeff • answer := by
  apply Prod.ext <;> simp [badCombine, v0, v1, v2, Expr.denote, Var.get, arithmetic, smul_eq_mul]

end Signatures.Runtime.WeightedAGM.Evaluate
