import Proofs.Runtime.EncodedReplay
import Proofs.Runtime.MixedReplay
import Proofs.Runtime.Sampling

/-! A charged family-indexed tape scan. It removes the first matching cell,
preserves every other cell in order, and returns the original tape on a miss. -/

namespace Signatures.Runtime.Schnorr.SeedTape

abbrev popState : Ty CryptoAtom :=
  .pair .bool (.pair Replay.Mixed.event (.list Replay.Mixed.event))

private def cell : Expr CryptoOp
    [Replay.Mixed.event, popState, .nat, .list Replay.Mixed.event] Replay.Mixed.event := .var .here
private def acc : Expr CryptoOp
    [Replay.Mixed.event, popState, .nat, .list Replay.Mixed.event] popState := .var (.there .here)
private def tag : Expr CryptoOp
    [Replay.Mixed.event, popState, .nat, .list Replay.Mixed.event] .nat :=
  .var (.there (.there .here))

private def keep : Expr CryptoOp
    [Replay.Mixed.event, popState, .nat, .list Replay.Mixed.event] popState :=
  .pair (.fst acc) (.pair (.fst (.snd acc)) (.cons cell (.snd (.snd acc))))

def popBody : Expr CryptoOp
    [Replay.Mixed.event, popState, .nat, .list Replay.Mixed.event] popState :=
  .branch (.fst acc) keep
    (.branch (.op .natEq (.pair (.fst cell) tag))
      (.pair (.bool true) (.pair cell (.snd (.snd acc)))) keep)

def popFold : Expr CryptoOp [.nat, .list Replay.Mixed.event] popState :=
  .fold (.var (.there .here))
    (.pair (.bool false) (.pair Replay.Mixed.emptyEvent .nil)) popBody

private def reverseRest : Expr CryptoOp [popState, .nat, .list Replay.Mixed.event]
    (.list Replay.Mixed.event) :=
  .letE (.snd (.snd (.var .here))) reverseList

/-- Result: found bit, removed cell (or zero default), remaining tape. -/
def popCode : Expr CryptoOp [.nat, .list Replay.Mixed.event] popState :=
  .letE popFold (.pair (.fst (.var .here))
    (.pair (.fst (.snd (.var .here))) reverseRest))

def pop {F : Type} (tag : Nat) (fallback : TapeCell F) :
    List (TapeCell F) → Bool × TapeCell F × List (TapeCell F)
  | [] => (false, fallback, [])
  | x :: xs => if x.1 = tag then (true, x, xs)
      else let r := pop tag fallback xs; (r.1, r.2.1, x :: r.2.2)

def popStep {F : Type} (tag : Nat) (s : Bool × TapeCell F × List (TapeCell F))
    (x : TapeCell F) : Bool × TapeCell F × List (TapeCell F) :=
  if s.1 then (true, s.2.1, x :: s.2.2)
  else if x.1 = tag then (true, x, s.2.2)
  else (false, s.2.1, x :: s.2.2)

theorem popStep_found {F : Type} (tag : Nat) (xs : List (TapeCell F))
    (answer : TapeCell F) (prior : List (TapeCell F)) :
    xs.foldl (popStep tag) (true, answer, prior) = (true, answer, xs.reverse ++ prior) := by
  induction xs generalizing prior with
  | nil => simp
  | cons x xs ih => simpa [popStep, List.reverse_cons, List.append_assoc] using ih (x :: prior)

theorem popStep_rest_length {F : Type} (tag : Nat) (xs : List (TapeCell F))
    (state : Bool × TapeCell F × List (TapeCell F)) :
    (xs.foldl (popStep tag) state).2.2.length ≤ state.2.2.length + xs.length := by
  induction xs generalizing state with
  | nil => simp
  | cons x xs ih =>
      have hstep : (popStep tag state x).2.2.length ≤ state.2.2.length + 1 := by
        unfold popStep
        split <;> (try split) <;> simp
      have h := ih (popStep tag state x)
      simp only [List.foldl_cons, List.length_cons]
      omega

/-- The accumulator retains the unremoved cells in reverse order. -/
theorem popStep_result {F : Type} (tag : Nat) (xs : List (TapeCell F))
    (fallback : TapeCell F) (prior : List (TapeCell F)) :
    let s := xs.foldl (popStep tag) (false, fallback, prior)
    (s.1, s.2.1, s.2.2.reverse) =
      let r := pop tag fallback xs
      (r.1, r.2.1, prior.reverse ++ r.2.2) := by
  induction xs generalizing prior with
  | nil => simp [pop]
  | cons x xs ih =>
      by_cases hx : x.1 = tag
      · simp [popStep, pop, hx, popStep_found]
      · simpa [popStep, pop, hx, List.reverse_cons, List.append_assoc] using ih (x :: prior)

theorem pop_length {F : Type} (tag : Nat) (fallback : TapeCell F) (xs : List (TapeCell F)) :
    (pop tag fallback xs).2.2.length ≤ xs.length := by
  induction xs with
  | nil => simp [pop]
  | cons x xs ih =>
      by_cases hx : x.1 = tag
      · simp [pop, hx]
      · simpa [pop, hx] using Nat.succ_le_succ ih

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem popBody_denote (cost : PrimitiveCosts) (x : TapeCell F)
    (s : Bool × TapeCell F × List (TapeCell F)) (n : Nat) (xs : List (TapeCell F)) :
    popBody.denote (arithmetic F G₁ G₂ K M cost) (x, s, n, xs, ()) = popStep n s x := by
  rcases s with ⟨found, answer, rest⟩
  cases found <;> by_cases hx : x.1 = n <;>
    simp [popBody, keep, popStep, cell, acc, tag, Expr.denote, Var.get, arithmetic, hx]

theorem popFold_denote (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    popFold.denote (arithmetic F G₁ G₂ K M cost) (n, xs, ()) =
      xs.foldl (popStep n) (false, (0, (0 : F), 0), []) := by
  change xs.foldl (fun s x => popBody.denote (arithmetic F G₁ G₂ K M cost)
    (x, s, n, xs, ())) (false, (0, (0 : F), 0), []) = _
  simp_rw [popBody_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

theorem popBody_steps (cost : PrimitiveCosts) (x : TapeCell F)
    (s : Bool × TapeCell F × List (TapeCell F)) (n : Nat) (xs : List (TapeCell F)) :
    (popBody.run (arithmetic F G₁ G₂ K M cost) (x, s, n, xs, ())).steps ≤ cost.natOp + 60 := by
  rcases s with ⟨found, answer, rest⟩
  cases found <;> by_cases hx : x.1 = n <;>
    simp [popBody, keep, cell, acc, tag, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, hx] <;>
    omega

theorem popFold_steps (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    (popFold.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())).steps ≤
      xs.length * (cost.natOp + 63) + cost.field + 20 := by
  have h := foldRun_steps_le
    (fun x s => popBody.run (arithmetic F G₁ G₂ K M cost) (x, s, n, xs, ()))
    (cost.natOp + 60) (fun x s => popBody_steps cost x s n xs)
    xs (false, (0, (0 : F), 0), [])
  dsimp [popFold, Expr.run, Var.get, Var.depth, Replay.Mixed.emptyEvent, arithmetic, CryptoOp.price] at h ⊢
  nlinarith

theorem popCode_denote (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    popCode.denote (arithmetic F G₁ G₂ K M cost) (n, xs, ()) = pop n (0, (0 : F), 0) xs := by
  simp only [popCode, Expr.denote, Var.get, reverseRest]
  rw [reverseList_denote, popFold_denote]
  simpa using popStep_result n xs (0, (0 : F), 0) []

/-- Includes the forward scan, rebuilding the remaining tape, and reversing
it back to its original order. -/
theorem popCode_steps (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    (popCode.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())).steps ≤
      xs.length * (cost.natOp + 70) + cost.field + 50 := by
  let s := (popFold.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())).value
  have hs : s = xs.foldl (popStep n) (false, (0, (0 : F), 0), []) :=
    (Expr.run_value _ _ _).trans (popFold_denote cost n xs)
  have hf := popFold_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost n xs
  have hl : s.2.2.length ≤ xs.length := by
    rw [hs]
    simpa using popStep_rest_length n xs (false, (0, (0 : F), 0), [])
  have hr := reverseList_steps_le (cell := Replay.Mixed.event)
    (Γ := [popState, .nat, .list Replay.Mixed.event]) (arithmetic F G₁ G₂ K M cost)
    s.2.2 (s, n, xs, ())
  dsimp only [popCode, Expr.run, Var.get, Var.depth, reverseRest]
  nlinarith

end Signatures.Runtime.Schnorr.SeedTape
