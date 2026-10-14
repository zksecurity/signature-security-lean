import Signatures.Runtime.ProximityWeight

/-! Executable term generation for the weighted lazy reductions. OOPS computes
successive powers by multiplication; Proximity walks its structural vector once.
Only the degree/dimension is unrolled into code. No topic or slot domain is
enumerated. Bounds charge this unrolling and the unary natural literals. -/

namespace Signatures.Runtime.WeightedAGM.Terms

open Weights

abbrev termTy (indexTy : Ty CryptoAtom) : Ty CryptoAtom := .pair indexTy scalar

/-- Generate consecutive polynomial terms from a running power. The retained
frames are ordinary syntax and will also be charged by the native compiler. -/
def oopsFrom (d : Nat) : Nat → Nat → {Γ : List (Ty CryptoAtom)} →
    Expr CryptoOp ([scalar, oopsMessage] ++ Γ) (.list (termTy (oopsKey d)))
  | 0, _, _ => .nil
  | n + 1, start, Γ =>
      .cons (.pair
        (.pair (.snd (.var (.there .here))) (.op (.finOfNat d) (.nat start)))
        (.var .here))
        (.letE (.var (.there .here))
          (.letE (.op .mul (.pair (.var (.there .here)) (.fst (.var .here))))
            (oopsFrom d n (start + 1) (Γ := [scalar, oopsMessage] ++ Γ))))

def oops (d : Nat) : Expr CryptoOp [oopsMessage] (.list (termTy (oopsKey d))) :=
  .letE (.op .one .unit) (oopsFrom d (d + 1) 0)

/-- Generate coordinate terms by peeling the tuple, preserving the source
coordinate order. Zero is reserved for the constant coordinate. -/
def proximityFrom (ell : Nat) : (n : Nat) → Nat → {Γ : List (Ty CryptoAtom)} →
    Expr CryptoOp ([proximityTupleMessage n] ++ Γ) (.list (termTy (proximityKey ell)))
  | 0, _, _ => .nil
  | n + 1, start, Γ =>
      .cons (.pair
        (.pair (.op (.finOfNat ell) (.nat start)) (.snd (.var .here)))
        (.fst (.fst (.var .here))))
        (.letE (.pair (.snd (.fst (.var .here))) (.snd (.var .here)))
          (proximityFrom ell n (start + 1) (Γ := [proximityTupleMessage (n + 1)] ++ Γ)))

def proximity (ell : Nat) :
    Expr CryptoOp [proximityTupleMessage ell] (.list (termTy (proximityKey ell))) :=
  .cons (.pair (.pair (.op (.finZero ell) .unit) (.snd (.var .here))) (.op .one .unit))
    (proximityFrom ell ell 1)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem oopsFrom_value (cost : PrimitiveCosts) (d n start : Nat) (p : F) (mt : F × K)
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((oopsFrom d n start).run (arithmetic F G₁ G₂ K M cost) (p, mt, env)).value =
      List.ofFn (fun k : Fin n =>
        ((mt.2, (⟨(start + k.val) % (d + 1), Nat.mod_lt _ (Nat.zero_lt_succ d)⟩ : Fin (d + 1))),
          p * mt.1 ^ k.val)) := by
  induction n generalizing start p Γ with
  | zero => simp [oopsFrom, Expr.run]
  | succ n ih =>
      have hi := ih (start + 1) (p * mt.1) (Γ := [scalar, oopsMessage] ++ Γ) (p, mt, env)
      dsimp [arithmetic] at hi
      simp only [oopsFrom, Expr.run, Var.get, arithmetic, hi, List.ofFn_succ]
      congr 1
      · simp
      · apply congrArg List.ofFn
        funext k
        simp [Fin.val_succ, pow_succ, mul_assoc, mul_comm]
        congr 1; omega

theorem oops_value (cost : PrimitiveCosts) (d : Nat) (mt : F × K) :
    ((oops d).run (arithmetic F G₁ G₂ K M cost) (mt, ())).value =
      OOPS.LazyAGM.terms d mt := by
  have h := oopsFrom_value (G₁ := G₁) (G₂ := G₂) (M := M) cost d (d + 1) 0 (1 : F) mt (Γ := []) ()
  change ((oopsFrom d (d + 1) 0 (Γ := [])).run (arithmetic F G₁ G₂ K M cost) (1, mt, ())).value = _
  rw [h]
  unfold OOPS.LazyAGM.terms
  apply congrArg List.ofFn
  funext k
  simp [Nat.mod_eq_of_lt k.isLt]

theorem proximityFrom_value (cost : PrimitiveCosts) (ell n start : Nat)
    (ms : (proximityTupleMessage n).Value (cryptoBase F G₁ G₂ K M))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((proximityFrom ell n start).run (arithmetic F G₁ G₂ K M cost) (ms, env)).value =
      List.ofFn (fun k : Fin n =>
        (((⟨(start + k.val) % (ell + 1), Nat.mod_lt _ (Nat.zero_lt_succ ell)⟩ : Fin (ell + 1)), ms.2),
          Tuple.decode n ms.1 k)) := by
  induction n generalizing start Γ with
  | zero => simp [proximityFrom, Expr.run]
  | succ n ih =>
      have hi := ih (start + 1) (ms.1.2, ms.2)
        (Γ := [proximityTupleMessage (n + 1)] ++ Γ) (ms, env)
      dsimp [arithmetic] at hi
      simp only [proximityFrom, Expr.run, Var.get, arithmetic, hi, List.ofFn_succ]
      simp only [Tuple.decode, Fin.cases_zero, Fin.cases_succ, Fin.val_zero,
        Fin.val_succ, Nat.add_zero, List.cons.injEq, true_and]
      apply congrArg List.ofFn
      funext k
      simp [Nat.add_comm, Nat.add_left_comm]

/-- Exact source terms after applying the established index encoding. -/
theorem proximity_value (cost : PrimitiveCosts) (ell : Nat)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M)) :
    ((proximity ell).run (arithmetic F G₁ G₂ K M cost) (ms, ())).value =
      (Proximity.LazyAGM.terms (proximityMessageEquiv ell ms)).map
        (Prod.map encodeProximityKey id) := by
  have h := proximityFrom_value (G₁ := G₁) (G₂ := G₂) (M := M) cost ell ell 1 ms (Γ := []) ()
  dsimp [arithmetic] at h
  simp only [proximity, Expr.run, arithmetic, Var.get, h, Proximity.LazyAGM.terms,
    List.map_cons, List.map_ofFn, Function.comp_def]
  apply congrArg (List.cons _)
  apply congrArg List.ofFn
  funext k
  simp [proximityMessageEquiv, Tuple.equiv, encodeProximityKey, Nat.add_comm]

def oopsFromTime (cost : PrimitiveCosts) (n start : Nat) : Nat :=
  n * (start + n + cost.natOp + cost.field + 24) + 1

theorem oopsFrom_steps_le (cost : PrimitiveCosts) (d n start : Nat) (p : F) (mt : F × K)
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((oopsFrom d n start).run (arithmetic F G₁ G₂ K M cost) (p, mt, env)).steps ≤
      oopsFromTime cost n start := by
  induction n generalizing start p Γ with
  | zero => simp [oopsFrom, Expr.run, oopsFromTime]
  | succ n ih =>
      have hi := ih (start + 1) (p * mt.1) (Γ := [scalar, oopsMessage] ++ Γ) (p, mt, env)
      dsimp [arithmetic, CryptoOp.price] at hi
      simp only [oopsFrom, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
      dsimp only [oopsFromTime] at hi ⊢
      nlinarith

def oopsTime (cost : PrimitiveCosts) (d : Nat) : Nat :=
  oopsFromTime cost (d + 1) 0 + cost.field + 3

theorem oops_steps_le (cost : PrimitiveCosts) (d : Nat) (mt : F × K) :
    ((oops d).run (arithmetic F G₁ G₂ K M cost) (mt, ())).steps ≤ oopsTime cost d := by
  have h := oopsFrom_steps_le (G₁ := G₁) (G₂ := G₂) (M := M) cost d (d + 1) 0 (1 : F) mt (Γ := []) ()
  dsimp [arithmetic, CryptoOp.price] at h
  simp only [oops, Expr.run, arithmetic, CryptoOp.price, oopsTime]
  omega

def proximityFromTime (cost : PrimitiveCosts) (n start : Nat) : Nat :=
  n * (start + n + cost.natOp + 20) + 1

theorem proximityFrom_steps_le (cost : PrimitiveCosts) (ell n start : Nat)
    (ms : (proximityTupleMessage n).Value (cryptoBase F G₁ G₂ K M))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    ((proximityFrom ell n start).run (arithmetic F G₁ G₂ K M cost) (ms, env)).steps ≤
      proximityFromTime cost n start := by
  induction n generalizing start Γ with
  | zero => simp [proximityFrom, Expr.run, proximityFromTime]
  | succ n ih =>
      have hi := ih (start + 1) (ms.1.2, ms.2)
        (Γ := [proximityTupleMessage (n + 1)] ++ Γ) (ms, env)
      dsimp [arithmetic, CryptoOp.price] at hi
      simp only [proximityFrom, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
      dsimp only [proximityFromTime] at hi ⊢
      nlinarith

def proximityTime (cost : PrimitiveCosts) (ell : Nat) : Nat :=
  proximityFromTime cost ell 1 + cost.natOp + cost.field + 9

theorem proximity_steps_le (cost : PrimitiveCosts) (ell : Nat)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M)) :
    ((proximity ell).run (arithmetic F G₁ G₂ K M cost) (ms, ())).steps ≤ proximityTime cost ell := by
  have h := proximityFrom_steps_le (G₁ := G₁) (G₂ := G₂) (M := M) cost ell ell 1 ms (Γ := []) ()
  dsimp [arithmetic, CryptoOp.price] at h
  simp only [proximity, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, proximityTime]
  omega

end Signatures.Runtime.WeightedAGM.Terms
