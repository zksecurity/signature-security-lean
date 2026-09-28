import Signatures.Runtime.Arithmetic
import Signatures.Runtime.Weakening

/-! Fixed-size first-order vectors. The type itself enforces the coordinate count; native
function-valued vectors are only a proof representation. Executed indexing uses ordinary
tuple projections, natural-number tests, and subtraction, not a function-application opcode. -/

namespace Signatures.Runtime

@[reducible] def tupleTy {Atom : Type} (cell : Ty Atom) : Nat → Ty Atom
  | 0 => .unit
  | n + 1 => .pair cell (tupleTy cell n)

namespace Tuple

variable {Atom : Type} {base : Atom → Type} {cell : Ty Atom}

def encode : (n : Nat) → (Fin n → cell.Value base) → (tupleTy cell n).Value base
  | 0, _ => ()
  | n + 1, f => (f 0, encode n (fun i => f i.succ))

def decode : (n : Nat) → (tupleTy cell n).Value base → (Fin n → cell.Value base)
  | 0, _ => Fin.elim0
  | n + 1, x => Fin.cases x.1 (decode n x.2)

theorem decode_encode (n : Nat) (f : Fin n → cell.Value base) : decode n (encode n f) = f := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa only [encode, decode, Fin.cases_succ] using congrFun (ih (fun j => f j.succ)) j

theorem encode_decode (n : Nat) (x : (tupleTy cell n).Value base) : encode n (decode n x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
      rcases x with ⟨x, xs⟩
      simp [encode, decode, ih]

def equiv (n : Nat) : (tupleTy cell n).Value base ≃ (Fin n → cell.Value base) where
  toFun := decode n
  invFun := encode n
  left_inv := encode_decode n
  right_inv := decode_encode n

end Tuple

def tupleIndex : (n : Nat) → Expr CryptoOp [.nat, tupleTy scalar n] scalar
  | 0 => .op .zero .unit
  | n + 1 =>
      .branch (.op .natEq (.pair (.var .here) (.nat 0))) (.fst (.var (.there .here)))
        (.letE (.snd (.var (.there .here)))
          (.letE (.op .natSub (.pair (.var (.there .here)) (.nat 1)))
            ((tupleIndex n).weakenTail [.nat, tupleTy scalar (n + 1)])))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem tupleIndex_value (cost : PrimitiveCosts) (n : Nat)
    (x : (tupleTy scalar n).Value (cryptoBase F G₁ G₂ K M)) (i : Fin n) :
    ((tupleIndex n).run (arithmetic F G₁ G₂ K M cost) (i.val, x, ())).value = Tuple.decode n x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [tupleIndex, Expr.run, Var.get, arithmetic, Tuple.decode]
      · have hp := (tupleIndex n).weakenTail_run (Δ := [.nat, tupleTy scalar (n + 1)])
          (arithmetic F G₁ G₂ K M cost) (j.val, x.2, ()) (j.val + 1, x, ())
        have hv := ih x.2 j
        simp only [Env.append] at hp
        dsimp [arithmetic] at hp hv
        simpa [tupleIndex, Expr.run, Var.get, arithmetic, Tuple.decode, hp,
          -Expr.run_value] using hv

def tupleIndexBound (cost : PrimitiveCosts) (n : Nat) : Nat :=
  n * (2 * cost.natOp + 16) + cost.field + 2

theorem tupleIndex_steps_le (cost : PrimitiveCosts) (n k : Nat)
    (x : (tupleTy scalar n).Value (cryptoBase F G₁ G₂ K M)) :
    ((tupleIndex n).run (arithmetic F G₁ G₂ K M cost) (k, x, ())).steps ≤ tupleIndexBound cost n := by
  induction n generalizing k with
  | zero => simp [tupleIndex, Expr.run, arithmetic, CryptoOp.price, tupleIndexBound]; omega
  | succ n ih =>
      have hp := (tupleIndex n).weakenTail_run (Δ := [.nat, tupleTy scalar (n + 1)])
        (arithmetic F G₁ G₂ K M cost) (k - 1, x.2, ()) (k, x, ())
      have hb := ih (k - 1) x.2
      simp only [Env.append] at hp
      dsimp [arithmetic, CryptoOp.price] at hp hb
      by_cases hk : k = 0 <;>
        simp only [tupleIndex, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, hp,
          hk, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false] <;>
        dsimp [tupleIndexBound] at hb ⊢ <;> nlinarith

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem tupleScalar_load_steps (n : Nat) (x : (tupleTy scalar n).Value (cryptoBase F G₁ G₂ K M)) :
    (Ty.load (tupleTy scalar n) x).steps = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tupleTy, Ty.load]
      have h := ih x.2
      omega

end Signatures.Runtime
