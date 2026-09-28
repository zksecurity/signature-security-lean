import Signatures.Runtime.Tuple
import Signatures.Runtime.Weights

/-! Uniformly bounded Proximity weights over a fixed-size structural vector. The machine
message type is equivalent to the native `(Fin ell -> F) x K`, so no message-length or
well-formedness assumption is added to the security game. -/

namespace Signatures.Runtime.Weights

abbrev proximityTupleMessage (ell : Nat) : Ty CryptoAtom := .pair (tupleTy scalar ell) key

def proximityMessageEquiv {F G₁ G₂ K M : Type} (ell : Nat) :
    (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M) ≃ ((Fin ell → F) × K) :=
  Equiv.prodCongr (Tuple.equiv (cell := scalar) (base := cryptoBase F G₁ G₂ K M) ell) (Equiv.refl K)

def decodeProximityKey {K : Type} {ell : Nat} (b : Fin (ell + 1) × K) : Option (Fin ell) × K :=
  (Fin.cases none some b.1, b.2)

theorem decodeProximityKey_encode {K : Type} {ell : Nat} (b : Option (Fin ell) × K) :
    decodeProximityKey (encodeProximityKey b) = b := by
  rcases b with ⟨b, slot⟩
  cases b <;> simp [decodeProximityKey, encodeProximityKey]

theorem encodeProximityKey_decode {K : Type} {ell : Nat} (b : Fin (ell + 1) × K) :
    encodeProximityKey (decodeProximityKey b) = b := by
  rcases b with ⟨b, slot⟩
  refine Fin.cases ?_ (fun i => ?_) b <;> rfl

def proximityKeyEquiv {K : Type} (ell : Nat) : (Fin (ell + 1) × K) ≃ (Option (Fin ell) × K) where
  toFun := decodeProximityKey
  invFun := encodeProximityKey
  left_inv := encodeProximityKey_decode
  right_inv := decodeProximityKey_encode

def proximityTuple (ell : Nat) :
    Expr CryptoOp [proximityKey ell, proximityTupleMessage ell] scalar :=
  .branch (.op .keyEq (.pair (.snd (.var .here)) (.snd (.var (.there .here)))))
    (.branch (.op .natEq (.pair (.op (.finVal ell) (.fst (.var .here))) (.nat 0)))
      (.op .one .unit)
      (.letE (.fst (.var (.there .here)))
        (.letE (.op .natSub (.pair (.op (.finVal ell) (.fst (.var (.there .here)))) (.nat 1)))
          ((tupleIndex ell).weakenTail [proximityKey ell, proximityTupleMessage ell]))))
    (.op .zero .unit)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem proximityTuple_native (cost : PrimitiveCosts) (ell : Nat)
    (b : Option (Fin ell) × K)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M)) :
    ((proximityTuple ell).run (arithmetic F G₁ G₂ K M cost) (encodeProximityKey b, ms, ())).value =
      Proximity.Proofs.coordinateWeight ell b (proximityMessageEquiv ell ms) := by
  rcases b with ⟨b, slot⟩
  cases b with
  | none =>
      by_cases ht : slot = ms.2 <;>
        simp [proximityTuple, Expr.run, Var.get, arithmetic, encodeProximityKey,
          Proximity.Proofs.coordinateWeight, proximityMessageEquiv, ht]
  | some j =>
      have hp := (tupleIndex ell).weakenTail_run
        (Δ := [proximityKey ell, proximityTupleMessage ell]) (arithmetic F G₁ G₂ K M cost)
        (j.val, ms.1, ()) (encodeProximityKey (some j, slot), ms, ())
      have hv := tupleIndex_value (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost ell ms.1 j
      simp only [Env.append] at hp
      dsimp [arithmetic, encodeProximityKey] at hp hv
      by_cases ht : slot = ms.2 <;>
        (try simp only [ht] at hp) <;>
        simp [proximityTuple, Expr.run, Var.get, arithmetic, encodeProximityKey,
          Proximity.Proofs.coordinateWeight, proximityMessageEquiv, Tuple.equiv, ht, hp, hv,
          -Expr.run_value]

def proximityTupleBound (cost : PrimitiveCosts) (ell : Nat) : Nat :=
  tupleIndexBound cost ell + cost.keyEq + 4 * cost.natOp + 28

theorem proximityTuple_steps_le (cost : PrimitiveCosts) (ell : Nat)
    (b : Fin (ell + 1) × K)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M)) :
    ((proximityTuple ell).run (arithmetic F G₁ G₂ K M cost) (b, ms, ())).steps ≤
      proximityTupleBound cost ell := by
  have hp := (tupleIndex ell).weakenTail_run
    (Δ := [proximityKey ell, proximityTupleMessage ell]) (arithmetic F G₁ G₂ K M cost)
    (b.1.val - 1, ms.1, ()) (b, ms, ())
  have hb := tupleIndex_steps_le (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost ell (b.1.val - 1) ms.1
  simp only [Env.append] at hp
  dsimp [arithmetic, CryptoOp.price] at hp hb
  by_cases ht : b.2 = ms.2 <;> by_cases hz : b.1.val = 0 <;>
    simp only [proximityTuple, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price,
      ht, hz, hp, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false] <;>
    dsimp [proximityTupleBound, tupleIndexBound] at hb ⊢ <;> nlinarith

theorem proximityTuple_decoded (cost : PrimitiveCosts) (ell : Nat)
    (b : Fin (ell + 1) × K)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M)) :
    ((proximityTuple ell).run (arithmetic F G₁ G₂ K M cost) (b, ms, ())).value =
      Proximity.Proofs.coordinateWeight ell (decodeProximityKey b) (proximityMessageEquiv ell ms) := by
  simpa only [encodeProximityKey_decode] using
    proximityTuple_native (G₁ := G₁) (G₂ := G₂) (M := M) cost ell (decodeProximityKey b) ms

end Signatures.Runtime.Weights
