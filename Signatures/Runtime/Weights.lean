import Signatures.Runtime.Arithmetic
import Signatures.Runtime.Index
import Signatures.Runtime.Weakening
import Signatures.BLS.Proofs.LazyAGM
import Signatures.OOPS.Proofs.LazyAGM
import Signatures.Proximity.Proofs.LazyAGM

/-! First-order weight programs for the three AGM signature families. OOPS topics and
degrees are structural inputs, not opaque projection callbacks. Bounded powers execute
charged arithmetic; Proximity coordinates use the linked-list indexing implementation. -/

namespace Signatures.Runtime.Weights

def bls : Expr CryptoOp [key, key] scalar :=
  .branch (.op .keyEq (.pair (.var .here) (.var (.there .here))))
    (.op .one .unit) (.op .zero .unit)

/-- Static unrolling uses one multiply/comparison per degree. Natural literals retain
their explicit unary load charge, so the conservative cost bound includes a quadratic term. -/
def power : Nat → Expr CryptoOp [scalar, .nat] scalar
  | 0 => .op .one .unit
  | n + 1 => .letE (power n)
      (.branch (.op .natLt (.pair (.nat n) (.var (.there (.there .here)))))
        (.op .mul (.pair (.var .here) (.var (.there .here)))) (.var .here))

abbrev oopsKey (d : Nat) : Ty CryptoAtom := .pair key (boundedNat d)
abbrev oopsMessage : Ty CryptoAtom := .pair scalar key

def oops (d : Nat) : Expr CryptoOp [oopsKey d, oopsMessage] scalar :=
  .branch (.op .keyEq (.pair (.fst (.var .here)) (.snd (.var (.there .here)))))
    (.letE (.op (.finVal d) (.snd (.var .here)))
      (.letE (.fst (.var (.there (.there .here))))
        ((power d).weakenTail [oopsKey d, oopsMessage])))
    (.op .zero .unit)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem bls_value (cost : PrimitiveCosts) (i m : K) :
    (bls.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value =
      BLS.Proofs.indicatorWeight (F := F) i m := by
  by_cases h : i = m <;> simp [bls, Expr.run, Var.get, arithmetic, BLS.Proofs.indicatorWeight, h]

theorem bls_steps (cost : PrimitiveCosts) (i m : K) :
    (bls.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps = cost.keyEq + cost.field + 8 := by
  by_cases h : i = m <;>
    simp [bls, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, h] <;> omega

theorem power_value (cost : PrimitiveCosts) (d n : Nat) (x : F) :
    ((power d).run (arithmetic F G₁ G₂ K M cost) (x, n, ())).value = x ^ min n d := by
  induction d with
  | zero => simp [power, Expr.run, arithmetic]
  | succ d ih =>
      dsimp [arithmetic] at ih
      by_cases hd : d < n
      · simp [power, Expr.run, Var.get, arithmetic, hd, ih, -Expr.run_value,
          Nat.min_eq_right (Nat.le_of_lt hd), pow_succ]
      · have hn : n ≤ d := Nat.le_of_not_gt hd
        simp [power, Expr.run, Var.get, arithmetic, hd, ih, -Expr.run_value,
          Nat.min_eq_left hn, Nat.min_eq_left (hn.trans (Nat.le_succ d))]

def powerBound (cost : PrimitiveCosts) (d : Nat) : Nat :=
  d * (d + cost.natOp + cost.field + 13) + cost.field + 2

theorem power_steps_le (cost : PrimitiveCosts) (d n : Nat) (x : F) :
    ((power d).run (arithmetic F G₁ G₂ K M cost) (x, n, ())).steps ≤ powerBound cost d := by
  induction d with
  | zero => simp [power, Expr.run, arithmetic, CryptoOp.price, powerBound]; omega
  | succ d ih =>
      dsimp [arithmetic, CryptoOp.price] at ih
      by_cases hd : d < n <;>
        simp only [power, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price,
          hd, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false] <;>
        dsimp [powerBound] at ih ⊢ <;> nlinarith

theorem oops_value (cost : PrimitiveCosts) (d : Nat) (b : K × Fin (d + 1)) (mt : F × K) :
    ((oops d).run (arithmetic F G₁ G₂ K M cost) (b, mt, ())).value =
      OOPS.Handle.oopsWMulti d b mt := by
  have hp := (power d).weakenTail_run (Δ := [oopsKey d, oopsMessage]) (arithmetic F G₁ G₂ K M cost)
    (mt.1, b.2.val, ()) (b, mt, ())
  simp only [Env.append] at hp
  have hv := power_value (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost d b.2.val mt.1
  dsimp [arithmetic] at hp hv
  by_cases ht : b.1 = mt.2 <;>
    simp [oops, Expr.run, Var.get, arithmetic, OOPS.Handle.oopsWMulti, ht, hp,
      hv,
      Nat.min_eq_left (Nat.le_of_lt_succ b.2.isLt), -Expr.run_value]

def oopsBound (cost : PrimitiveCosts) (d : Nat) : Nat :=
  powerBound cost d + cost.natOp + cost.keyEq + 17

theorem oops_steps_le (cost : PrimitiveCosts) (d : Nat) (b : K × Fin (d + 1)) (mt : F × K) :
    ((oops d).run (arithmetic F G₁ G₂ K M cost) (b, mt, ())).steps ≤ oopsBound cost d := by
  have hp := (power d).weakenTail_run (Δ := [oopsKey d, oopsMessage]) (arithmetic F G₁ G₂ K M cost)
    (mt.1, b.2.val, ()) (b, mt, ())
  simp only [Env.append] at hp
  have hb := power_steps_le (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost d b.2.val mt.1
  dsimp [arithmetic, CryptoOp.price] at hp hb
  by_cases ht : b.1 = mt.2 <;>
    simp only [oops, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, ht,
      decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false, hp] <;>
    dsimp [oopsBound, powerBound] at hb ⊢ <;> nlinarith

abbrev proximityKey (ell : Nat) : Ty CryptoAtom := .pair (boundedNat ell) key
abbrev proximityMessage : Ty CryptoAtom := .pair (.list scalar) key

def proximity (ell : Nat) : Expr CryptoOp [proximityKey ell, proximityMessage] scalar :=
  .branch (.op .keyEq (.pair (.snd (.var .here)) (.snd (.var (.there .here)))))
    (.branch (.op .natEq (.pair (.op (.finVal ell) (.fst (.var .here))) (.nat 0)))
      (.op .one .unit)
      (.letE (.fst (.var (.there .here)))
        (.letE (.op .zero .unit)
          (.letE (.op .natSub (.pair
            (.op (.finVal ell) (.fst (.var (.there (.there .here))))) (.nat 1)))
            ((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail
              [proximityKey ell, proximityMessage])))))
    (.op .zero .unit)

theorem proximity_value (cost : PrimitiveCosts) (ell : Nat)
    (b : Fin (ell + 1) × K) (ms : List F × K) :
    ((proximity ell).run (arithmetic F G₁ G₂ K M cost) (b, ms, ())).value =
      if b.2 = ms.2 then (if b.1.val = 0 then 1 else (ms.1[b.1.val - 1]?).getD 0) else 0 := by
  have hp := (index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail_run
    (Δ := [proximityKey ell, proximityMessage]) (arithmetic F G₁ G₂ K M cost)
    (b.1.val - 1, 0, ms.1, ()) (b, ms, ())
  simp only [Env.append] at hp
  have hi : ((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).run
      (arithmetic F G₁ G₂ K M cost) (b.1.val - 1, 0, ms.1, ())).value =
      (ms.1[b.1.val - 1]?).getD 0 := by
    rw [Expr.run_value]
    exact index_denote _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) _ _ _
  dsimp [arithmetic] at hp hi
  by_cases ht : b.2 = ms.2 <;> by_cases hz : b.1.val = 0 <;>
    simp [proximity, Expr.run, Var.get, arithmetic, ht, hz, hp, hi, -Expr.run_value]

def proximityBound (cost : PrimitiveCosts) (len : Nat) : Nat :=
  len * (2 * cost.natOp + 26) + cost.keyEq + 4 * cost.natOp + cost.field + 45

theorem proximity_steps_le (cost : PrimitiveCosts) (ell : Nat)
    (b : Fin (ell + 1) × K) (ms : List F × K) :
    ((proximity ell).run (arithmetic F G₁ G₂ K M cost) (b, ms, ())).steps ≤
      proximityBound cost ms.1.length := by
  have hp := (index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail_run
    (Δ := [proximityKey ell, proximityMessage]) (arithmetic F G₁ G₂ K M cost)
    (b.1.val - 1, 0, ms.1, ()) (b, ms, ())
  simp only [Env.append] at hp
  have hb := index_steps_le (cell := scalar) (arithmetic F G₁ G₂ K M cost)
    CryptoOp.natEq CryptoOp.natSub cost.natOp (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (b.1.val - 1) 0 ms.1
  dsimp [arithmetic, CryptoOp.price] at hp hb
  by_cases ht : b.2 = ms.2 <;> by_cases hz : b.1.val = 0 <;>
    simp only [proximity, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, ht, hz,
      decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false, hp] <;>
    dsimp [proximityBound] <;> nlinarith

/-- Zero represents the constant coordinate; the remaining tags represent Fin ell. -/
def encodeProximityKey {ell : Nat} (b : Option (Fin ell) × K) : Fin (ell + 1) × K :=
  match b.1 with
  | none => (0, b.2)
  | some k => (⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩, b.2)

omit [DecidableEq K] in
theorem encodeProximityKey_injective (ell : Nat) :
    Function.Injective (encodeProximityKey (K := K) (ell := ell)) := by
  intro ⟨x, k⟩ ⟨y, l⟩ h
  cases x <;> cases y <;> simp_all [encodeProximityKey, Prod.ext_iff, Fin.ext_iff]

/-- Proof-only decoding; executable coordinate access is the index program above. -/
def decodeProximityMessage (ell : Nat) (ms : List F × K) : (Fin ell → F) × K :=
  (fun k => (ms.1[k.val]?).getD 0, ms.2)

theorem proximity_native (cost : PrimitiveCosts) (ell : Nat)
    (b : Option (Fin ell) × K) (ms : List F × K) :
    ((proximity ell).run (arithmetic F G₁ G₂ K M cost) (encodeProximityKey b, ms, ())).value =
      Proximity.Proofs.coordinateWeight ell b (decodeProximityMessage ell ms) := by
  rw [proximity_value]
  rcases b with ⟨b, slot⟩
  cases b <;> by_cases ht : slot = ms.2 <;>
    simp [encodeProximityKey, decodeProximityMessage, Proximity.Proofs.coordinateWeight, ht]

omit [DecidableEq F] [DecidableEq K] in
theorem decodeProximityMessage_ofFn (ell : Nat) (m : Fin ell → F) (slot : K) :
    decodeProximityMessage ell (List.ofFn m, slot) = (m, slot) := by
  simp [decodeProximityMessage]

end Signatures.Runtime.Weights
