import Proofs.Runtime.SeedTape

/-! Reset a single seed family for the second pass. The compiled scan retains
its selected prefix and all other families, then appends the replacement answer. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

def trim {F : Type} (tag : Nat) (n : Nat) : List (TapeCell F) → Nat × List (TapeCell F)
  | [] => (n, [])
  | x :: xs =>
      if x.1 = tag then
        if n = 0 then trim tag n xs
        else let r := trim tag (n - 1) xs; (r.1, x :: r.2)
      else let r := trim tag n xs; (r.1, x :: r.2)

def trimStep {F : Type} (tag : Nat) (s : Nat × List (TapeCell F)) (x : TapeCell F) :
    Nat × List (TapeCell F) :=
  if x.1 = tag then if s.1 = 0 then s else (s.1 - 1, x :: s.2)
  else (s.1, x :: s.2)

theorem trim_fold {F : Type} (tag n : Nat) (xs prior : List (TapeCell F)) :
    xs.foldl (trimStep tag) (n, prior) =
      ((trim tag n xs).1, (trim tag n xs).2.reverse ++ prior) := by
  induction xs generalizing n prior with
  | nil => simp [trim]
  | cons x xs ih =>
      by_cases hx : x.1 = tag <;> cases n <;>
        simp [trimStep, trim, hx, ih, List.reverse_cons, List.append_assoc]

theorem trim_length {F : Type} (tag n : Nat) (xs : List (TapeCell F)) :
    (trim tag n xs).2.length ≤ xs.length := by
  induction xs generalizing n with
  | nil => simp [trim]
  | cons x xs ih =>
      by_cases hx : x.1 = tag <;> cases n <;> simp [trim, hx] <;>
        first | exact ih _ | exact (ih _).trans (by omega)

theorem values_trim {F : Type} (i : (replaySpec F).Domain) (n : Nat) (xs : List (TapeCell F)) :
    values i (trim (familyTag i) n xs).2 = (values i xs).take n := by
  induction xs generalizing n with
  | nil => simp [trim, values]
  | cons x xs ih =>
      by_cases hx : x.1 = familyTag i <;> cases n <;> simp [trim, values, hx, ih]

theorem values_trim_other {F : Type} (i j : (replaySpec F).Domain) (hji : j ≠ i)
    (n : Nat) (xs : List (TapeCell F)) :
    values j (trim (familyTag i) n xs).2 = values j xs := by
  have ht : familyTag i ≠ familyTag j := fun h => hji (familyTag_injective h).symm
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.1 = familyTag i <;> cases n <;> simp [trim, values, hx, ht, ih]

theorem values_append {F : Type} (i : (replaySpec F).Domain) (xs ys : List (TapeCell F)) :
    values i (xs ++ ys) = values i xs ++ values i ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases hx : x.1 = familyTag i <;> simp [values, hx, ih]

def reset {F : Type} (tag n : Nat) (answer : TapeCell F) (xs : List (TapeCell F)) :
    List (TapeCell F) := (trim tag n xs).2 ++ [answer]

theorem reset_length {F : Type} (tag n : Nat) (answer : TapeCell F) (xs : List (TapeCell F)) :
    (reset tag n answer xs).length ≤ xs.length + 1 := by
  simpa [reset] using Nat.add_le_add_right (trim_length tag n xs) 1

/-- This identity preserves every private family, including its unconsumed suffix. -/
theorem toSeed_reset {F : Type} [Zero F] (i : (replaySpec F).Domain) (n : Nat)
    (answer : (replaySpec F).Range i) (xs : List (TapeCell F)) :
    toSeed (reset (familyTag i) n (encodeReply i answer) xs) =
      ((toSeed xs).takeAtIndex i n).addValue i answer := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [toSeed, reset, values_append, values_trim, values, familyTag_encode, decode_encode,
      QuerySeed.addValue]
  · have ht : familyTag i ≠ familyTag j := fun h => hji (familyTag_injective h).symm
    simp [toSeed, reset, values_append, values_trim_other i j hji, values, familyTag_encode, ht,
      QuerySeed.addValue, QuerySeed.addValues, QuerySeed.update_of_ne, hji]

abbrev trimState : Ty CryptoAtom := .pair .nat (.list Replay.Mixed.event)

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

def trimBody {Γ} : Expr CryptoOp
    (Replay.Mixed.event :: trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Γ) trimState :=
  .branch (.op .natEq (.pair (.fst v0) v2))
    (.branch (.op .natEq (.pair (.fst v1) (.nat 0))) v1
      (.pair (.op .natSub (.pair (.fst v1) (.nat 1))) (.cons v0 (.snd v1))))
    (.pair (.fst v1) (.cons v0 (.snd v1)))

def trimFold {Γ} : Expr CryptoOp (.nat :: .nat :: .list Replay.Mixed.event :: Γ) trimState :=
  .fold v2 (.pair v1 .nil) trimBody

def resetCode : Expr CryptoOp [.nat, .nat, .list Replay.Mixed.event, Replay.Mixed.event]
    (.list Replay.Mixed.event) :=
  .letE trimFold (.letE
    (.cons (.var (.there (.there (.there (.there .here))))) (.snd v0)) reverseList)

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem trimBody_denote (cost : PrimitiveCosts) {Γ} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (x : TapeCell F) (s : Nat × List (TapeCell F)) (tag n : Nat) (xs : List (TapeCell F)) :
    trimBody.denote (arithmetic F G₁ G₂ K M cost) (x, s, tag, n, xs, env) = trimStep tag s x := by
  by_cases hx : x.1 = tag <;> by_cases hn : s.1 = 0 <;>
    simp [trimBody, trimStep, Expr.denote, v0, v1, v2, Var.get, arithmetic, hx, hn]

theorem trimFold_denote (cost : PrimitiveCosts) {Γ} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (tag n : Nat) (xs : List (TapeCell F)) :
    trimFold.denote (arithmetic F G₁ G₂ K M cost) (tag, n, xs, env) =
      ((trim tag n xs).1, (trim tag n xs).2.reverse) := by
  change xs.foldl (fun s x => trimBody.denote (arithmetic F G₁ G₂ K M cost)
    (x, s, tag, n, xs, env)) (n, []) = _
  simp_rw [trimBody_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  simpa using trim_fold tag n xs []

theorem resetCode_denote (cost : PrimitiveCosts) (tag n : Nat) (xs : List (TapeCell F))
    (answer : TapeCell F) :
    resetCode.denote (arithmetic F G₁ G₂ K M cost) (tag, n, xs, answer, ()) =
      reset tag n answer xs := by
  simp only [resetCode, Expr.denote, Var.get, v0]
  rw [reverseList_denote, trimFold_denote]
  simp [reset]

theorem trimBody_steps (cost : PrimitiveCosts) {Γ} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (x : TapeCell F) (s : Nat × List (TapeCell F)) (tag n : Nat) (xs : List (TapeCell F)) :
    (trimBody.run (arithmetic F G₁ G₂ K M cost) (x, s, tag, n, xs, env)).steps ≤
      3 * cost.natOp + 70 := by
  by_cases hx : x.1 = tag <;> by_cases hn : s.1 = 0 <;>
    simp [trimBody, Expr.run, v0, v1, v2, Var.get, Var.depth, arithmetic, CryptoOp.price, hx, hn] <;>
      omega

theorem trimFold_steps (cost : PrimitiveCosts) {Γ} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (tag n : Nat) (xs : List (TapeCell F)) :
    (trimFold.run (arithmetic F G₁ G₂ K M cost) (tag, n, xs, env)).steps ≤
      xs.length * (3 * cost.natOp + 73) + 10 := by
  have h := foldRun_steps_le
    (fun x s => trimBody.run (arithmetic F G₁ G₂ K M cost) (x, s, tag, n, xs, env))
    (3 * cost.natOp + 70) (fun x s => trimBody_steps cost env x s tag n xs) xs (n, [])
  dsimp [trimFold, Expr.run, v0, v1, v2, Var.get, Var.depth] at h ⊢
  nlinarith

theorem resetCode_steps (cost : PrimitiveCosts) (tag n : Nat) (xs : List (TapeCell F))
    (answer : TapeCell F) :
    (resetCode.run (arithmetic F G₁ G₂ K M cost) (tag, n, xs, answer, ())).steps ≤
      xs.length * (3 * cost.natOp + 80) + 100 := by
  let s := ((trimFold (Γ := [Replay.Mixed.event])).run
    (arithmetic F G₁ G₂ K M cost) (tag, n, xs, answer, ())).value
  have hs : s.2.length ≤ xs.length := by
    dsimp [s]
    rw [Expr.run_value, trimFold_denote]
    simpa using trim_length tag n xs
  have hf := trimFold_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost (Γ := [Replay.Mixed.event]) (answer, ()) tag n xs
  have hr := reverseList_steps_le (cell := Replay.Mixed.event)
    (Γ := [trimState, .nat, .nat, .list Replay.Mixed.event, Replay.Mixed.event])
    (arithmetic F G₁ G₂ K M cost) (answer :: s.2) (s, tag, n, xs, answer, ())
  dsimp only [resetCode, Expr.run, v0, Var.get, Var.depth]
  simp only [List.length_cons] at hr
  nlinarith

end Signatures.Runtime.Schnorr.SeedTape
