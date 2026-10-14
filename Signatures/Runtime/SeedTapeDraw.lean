import Signatures.Runtime.SeedTape

/-! Executable family-indexed draws. Every request scans the finite encoded tape;
a hit consumes one cell and a miss invokes the underlying primitive sampler.
The scan, codecs, literal tags, register frames and store operations are charged. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

abbrev store : Ty CryptoAtom := .list Replay.Mixed.event

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)

def draw {a : Ty CryptoAtom} (tag : Nat) (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [Replay.Mixed.event] a) :
    Program CryptoOp (Machine.Effect store) [.unit] a :=
  .bind (.query .read .unit)
    (.bind (.call (.ret popCode) (.cons (.nat tag) (.cons v0 .nil)))
      (.branch (.fst v0)
        (.bind (.query .write (.snd (.snd v0)))
          (.call (.ret decode) (.cons (.fst (.snd v1)) .nil)))
        (.query sample .unit)))

def scalarDraw (live : Bool) := draw (if live then 1 else 0) .scalar Replay.Mixed.scalarDecode
def uniformDraw (n : Nat) := draw (n + 2) (.uniform n) (Replay.Mixed.uniformDecode n)

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

private theorem state_bind {S A B : Type} (x : StateT S ProbComp A)
    (k : A → StateT S ProbComp B) (s : S) :
    (x >>= k) s = (x s >>= fun p => k p.1 p.2) := rfl

private theorem state_pure {S A : Type} (a : A) (s : S) :
    (pure a : StateT S ProbComp A) s = pure (a, s) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem draw_hit (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice tag : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [Replay.Mixed.event] a) (xs : List (TapeCell F))
    (h : (pop tag (0, (0 : F), 0) xs).1 = true) :
    (((draw tag sample decode).run (arithmetic F G₁ G₂ K M cost)
      (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run xs) =
      let scan := popCode.run (arithmetic F G₁ G₂ K M cost) (tag, xs, ())
      let answer := decode.run (arithmetic F G₁ G₂ K M cost) (scan.value.2.1, ())
      pure (⟨answer.value, scan.steps + answer.steps + tag + readPrice + writePrice + 29⟩,
        scan.value.2.2) := by
  have hv := (Expr.run_value (arithmetic F G₁ G₂ K M cost) popCode (tag, xs, ())).trans
    (popCode_denote cost tag xs)
  unfold draw
  generalize popCode = scan at hv ⊢
  dsimp [Program.run, Args.run, Expr.run, v0, v1, Var.get, Var.depth,
    StateT.run, StateT.bind, StateT.pure, Machine.pricedStoreEffects]
  simp only [pure_bind, show (scan.run (arithmetic F G₁ G₂ K M cost)
    (tag, xs, ())).value.1 = true from by rw [hv]; exact h, ite_true]
  simp only [state_bind, state_pure, Machine.pricedStoreEffects, pure_bind]
  congr 1
  apply Prod.ext
  · apply congrArg (Run.mk _)
    omega
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem draw_miss (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice tag : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [Replay.Mixed.event] a)
    (random : ProbComp (a.Value (cryptoBase F G₁ G₂ K M))) (price : Nat)
    (hsample : ∀ s, (Machine.pricedStoreEffects sampling store readPrice writePrice sample ()).run s =
      (fun x => (⟨x, price⟩, s)) <$> random)
    (xs : List (TapeCell F)) (h : (pop tag (0, (0 : F), 0) xs).1 = false) :
    (((draw tag sample decode).run (arithmetic F G₁ G₂ K M cost)
      (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run xs) =
      (fun answer => (⟨answer,
        (popCode.run (arithmetic F G₁ G₂ K M cost) (tag, xs, ())).steps +
          price + tag + readPrice + 17⟩, xs)) <$> random := by
  have hv := (Expr.run_value (arithmetic F G₁ G₂ K M cost) popCode (tag, xs, ())).trans
    (popCode_denote cost tag xs)
  unfold draw
  generalize popCode = scan at hv ⊢
  dsimp [Program.run, Args.run, Expr.run, v0, v1, Var.get, Var.depth]
  generalize Machine.pricedStoreEffects (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    sampling store readPrice writePrice sample () = action at hsample ⊢
  dsimp [StateT.run, StateT.bind, StateT.pure, Machine.pricedStoreEffects] at hsample ⊢
  simp only [state_bind, state_pure, pure_bind, show (scan.run (arithmetic F G₁ G₂ K M cost)
    (tag, xs, ())).value.1 = false from by rw [hv]; exact h, Bool.false_eq_true, ite_false]
  rw [hsample]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  congr 1
  funext answer
  congr 1
  apply Prod.ext
  · apply congrArg (Run.mk _)
    omega
  · rfl

def drawBound (cost : PrimitiveCosts) (tag price cDecode length : Nat)
    (readPrice : Nat := 1) (writePrice : Nat := 1) : Nat :=
  length * (cost.natOp + 70) + cost.field + tag + price + cDecode +
    readPrice + writePrice + 79

theorem draw_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice tag : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [Replay.Mixed.event] a)
    (random : ProbComp (a.Value (cryptoBase F G₁ G₂ K M))) (price cDecode : Nat)
    (hsample : ∀ s, (Machine.pricedStoreEffects sampling store readPrice writePrice sample ()).run s =
      (fun x => (⟨x, price⟩, s)) <$> random)
    (hdecode : ∀ cell, (decode.run (arithmetic F G₁ G₂ K M cost) (cell, ())).steps ≤ cDecode)
    (xs : List (TapeCell F))
    (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) × List (TapeCell F))
    (hz : z ∈ support (((draw tag sample decode).run (arithmetic F G₁ G₂ K M cost)
      (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run xs)) :
    z.1.steps ≤ drawBound cost tag price cDecode xs.length readPrice writePrice ∧
      z.2.length ≤ xs.length := by
  have hs := popCode_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost tag xs
  cases h : (pop tag (0, (0 : F), 0) xs).1 with
  | true =>
      rw [draw_hit cost sampling readPrice writePrice tag sample decode xs h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst z
      have hd := hdecode (popCode.run (arithmetic F G₁ G₂ K M cost) (tag, xs, ())).value.2.1
      constructor
      · dsimp [drawBound]; omega
      · simp only [Expr.run_value]
        rw [popCode_denote]
        exact pop_length tag (0, (0 : F), 0) xs
  | false =>
      rw [draw_miss cost sampling readPrice writePrice tag sample decode random price hsample xs h] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨answer, _, rfl⟩ := hz
      exact ⟨by dsimp [drawBound]; omega, le_rfl⟩

theorem draw_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice tag : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [Replay.Mixed.event] a)
    (random : ProbComp (a.Value (cryptoBase F G₁ G₂ K M))) (price : Nat)
    (hsample : ∀ s, (Machine.pricedStoreEffects sampling store readPrice writePrice sample ()).run s =
      (fun x => (⟨x, price⟩, s)) <$> random)
    (xs : List (TapeCell F)) :
    (fun z => (z.1.value, z.2)) <$>
      (((draw tag sample decode).run (arithmetic F G₁ G₂ K M cost)
        (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run xs) =
      let r := pop tag (0, (0 : F), 0) xs
      if r.1 then pure (decode.denote (arithmetic F G₁ G₂ K M cost) (r.2.1, ()), r.2.2)
      else (fun answer => (answer, xs)) <$> random := by
  cases h : (pop tag (0, (0 : F), 0) xs).1 with
  | true =>
      rw [draw_hit cost sampling readPrice writePrice tag sample decode xs h]
      simp only [h, ite_true, map_pure, Expr.run_value]
      rw [popCode_denote]
  | false =>
      rw [draw_miss cost sampling readPrice writePrice tag sample decode random price hsample xs h]
      simp only [h, Bool.false_eq_true, ite_false, Functor.map_map]

/-- Lower the three typed randomness families to their actual primitive samplers. -/
def samples : QueryImpl (replaySpec F) ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr ()) => $ᵗ F
  | .inr () => $ᵗ F

theorem scalarDraw_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice : Nat) (live : Bool) (xs : List (TapeCell F)) :
    (fun z => (z.1.value, z.2)) <$>
      (((scalarDraw live).run (arithmetic F G₁ G₂ K M cost)
        (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run xs) =
      simulateQ samples (if live then (oracle (.inr ())).run xs
        else (oracle (.inl (.inr ()))).run xs) := by
  rw [scalarDraw, draw_erase cost sampling readPrice writePrice _ .scalar
    Replay.Mixed.scalarDecode ($ᵗ F) sampling.scalar (fun _ => rfl)]
  cases live <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, oracle, familyTag, StateT.run]
  all_goals split <;> simp_all [samples, decodeReply,
    Replay.Mixed.scalarDecode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

theorem uniformDraw_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice n : Nat) (xs : List (TapeCell F)) :
    (fun z => (z.1.value, z.2)) <$>
      (((uniformDraw n).run (arithmetic F G₁ G₂ K M cost)
        (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run xs) =
      simulateQ samples ((oracle (.inl (.inl n))).run xs) := by
  rw [uniformDraw, draw_erase cost sampling readPrice writePrice _ (.uniform n)
    (Replay.Mixed.uniformDecode n) (liftM (unifSpec.query n)) (sampling.uniform n) (fun _ => rfl)]
  simp only [oracle, familyTag, StateT.run]
  split <;> simp_all [samples, decodeReply,
    Replay.Mixed.uniformDecode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

end Signatures.Runtime.Schnorr.SeedTape
