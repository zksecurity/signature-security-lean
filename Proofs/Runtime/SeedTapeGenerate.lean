import Proofs.Runtime.EncodedSampling
import Proofs.Runtime.SeedTapeDraw
import Proofs.Runtime.SeedTapeReset

/-! Compiled seed generation follows the explicit family list. Repeated families
contribute repeated blocks in the reference sampler's order. All sampling,
encoding, concatenation, capacity literals and procedure frames are charged. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

abbrev Family := (Nat ⊕ Unit) ⊕ Unit

def familyBlock (state : Ty CryptoAtom) : Family →
    Program CryptoOp (Machine.Effect state) [.nat] (.list Replay.Mixed.event)
  | .inl (.inl n) => encodedTable (.uniform n) (Replay.Mixed.uniformEncode n)
  | .inl (.inr ()) => encodedTable .scalar (Replay.Mixed.scalarEncode false)
  | .inr () => encodedTable .scalar (Replay.Mixed.scalarEncode true)

def familyPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) : Family → Nat
  | .inl (.inl n) => sampling.uniform n + n + cost.field + cost.natOp + 9
  | .inl (.inr ()) | .inr () => sampling.scalar + 6

def generateCode (state : Ty CryptoAtom) (capacity : Family → Nat) :
    List Family → Program CryptoOp (Machine.Effect state) [] (.list Replay.Mixed.event)
  | [] => .ret .nil
  | i :: is =>
      .bind (.call (familyBlock state i) (.cons (.nat (capacity i)) .nil))
        (.bind (.call (generateCode state capacity is) .nil)
          (.call (.ret appendCode)
            (.cons (.var (.there .here)) (.cons (.var .here) .nil))))

def generatePrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (capacity : Family → Nat) : List Family → Nat
  | [] => 2
  | i :: is => capacity i * (familyPrice cost sampling i + 40) + 41 +
      generatePrice cost sampling capacity is

def seedLength (capacity : Family → Nat) (is : List Family) : Nat := (is.map capacity).sum

def generate {F : Type} [Zero F] [SampleableType F] (capacity : Family → Nat) :
    List Family → ProbComp (List (TapeCell F))
  | [] => pure []
  | i :: is => do
      let xs ← replicate (capacity i) (samples i)
      let rest ← generate capacity is
      pure (xs.map (encodeReply i) ++ rest)

theorem samples_uniform {F : Type} [SampleableType F] (i : Family) :
    samples (F := F) i = $ᵗ (replaySpec F).Range i := by
  rcases i with (n | ⟨⟩) | ⟨⟩ <;> rfl

theorem toSeed_prepend {F : Type} [Zero F] (i : Family)
    (xs : List ((replaySpec F).Range i)) (rest : List (TapeCell F)) :
    toSeed (xs.map (encodeReply i) ++ rest) = (toSeed rest).prependValues xs := by
  funext j
  by_cases hji : j = i
  · subst j
    have hv : values i (xs.map (encodeReply i)) = xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [values, familyTag_encode, decode_encode, ih]
    simp [toSeed, values_append, hv]
  · have ht : familyTag i ≠ familyTag j := fun h => hji (familyTag_injective h).symm
    have hv : values j (xs.map (encodeReply i)) = [] := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [values, familyTag_encode, ht, ih]
    simp [toSeed, values_append, hv, QuerySeed.prependValues_of_ne _ _ hji]

/-- Equality of computations, including the order of every primitive draw. -/
theorem toSeed_generate {F : Type} [Zero F] [SampleableType F]
    (capacity : Family → Nat) (is : List Family) :
    toSeed <$> generate (F := F) capacity is = generateSeed (replaySpec F) capacity is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [generate, generateSeed_cons, samples_uniform, map_bind, map_pure]
      congr 1
      funext xs
      rw [← ih]
      simp only [bind_map_left, toSeed_prepend]

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

set_option backward.isDefEq.respectTransparency false in
theorem familyBlock_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (state : Ty CryptoAtom) (i : Family) (n : Nat) (s : state.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => (p.1.value, p.2)) <$>
        ((familyBlock state i).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling state) (n, ())).run s =
      (fun xs => (xs.map (encodeReply i), s)) <$> replicate n (samples i) := by
  rcases i with (k | ⟨⟩) | ⟨⟩
  · have h := encodedTable_erase (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling state)
      (.uniform k) (Replay.Mixed.uniformEncode k) (liftM (unifSpec.query k))
      (sampling.uniform k) (fun _ => rfl) n s
    simp only [familyBlock, samples,
      Replay.Mixed.uniformEncode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)] at h ⊢
    convert h using 1
    rfl
  · have h := encodedTable_erase (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling state)
      .scalar (Replay.Mixed.scalarEncode false) ($ᵗ F) sampling.scalar (fun _ => rfl) n s
    simp only [familyBlock, samples,
      Replay.Mixed.scalarEncode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
      Bool.false_eq_true, ite_false] at h ⊢
    convert h using 1
    rfl
  · have h := encodedTable_erase (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling state)
      .scalar (Replay.Mixed.scalarEncode true) ($ᵗ F) sampling.scalar (fun _ => rfl) n s
    simp only [familyBlock, samples,
      Replay.Mixed.scalarEncode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
      ite_true] at h ⊢
    convert h using 1
    rfl

theorem familyBlock_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (state : Ty CryptoAtom) (i : Family) (n : Nat) (s : state.Value (cryptoBase F G₁ G₂ K M))
    (out : Run (List (TapeCell F)) × state.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((familyBlock state i).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling state) (n, ())).run s)) :
    out.1.steps ≤ n * (familyPrice cost sampling i + 25) + 10 ∧
      out.1.value.length = n ∧ out.2 = s := by
  rcases i with (k | ⟨⟩) | ⟨⟩
  · have h := encodedTable_bound (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling state)
      (.uniform k) (Replay.Mixed.uniformEncode k) (liftM (unifSpec.query k)) (sampling.uniform k)
      (k + cost.field + cost.natOp + 9) (fun _ => rfl)
      (fun x => le_of_eq (Replay.Mixed.uniformEncode_steps cost k x)) n s out hout
    simpa only [familyPrice, Nat.add_assoc] using h
  · exact encodedTable_bound (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling state)
      .scalar (Replay.Mixed.scalarEncode false) ($ᵗ F) sampling.scalar 6 (fun _ => rfl)
      (Replay.Mixed.scalarEncode_steps cost false) n s out hout
  · exact encodedTable_bound (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling state)
      .scalar (Replay.Mixed.scalarEncode true) ($ᵗ F) sampling.scalar 6 (fun _ => rfl)
      (Replay.Mixed.scalarEncode_steps cost true) n s out hout

set_option backward.isDefEq.respectTransparency false in
theorem generateCode_cons_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (state : Ty CryptoAtom) (capacity : Family → Nat) (i : Family) (is : List Family)
    (s : state.Value (cryptoBase F G₁ G₂ K M)) :
    ((generateCode state capacity (i :: is)).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling state) ()).run s = (do
      let first ← ((familyBlock state i).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling state) (capacity i, ())).run s
      let rest ← ((generateCode state capacity is).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling state) ()).run first.2
      let copied := appendCode.run (arithmetic F G₁ G₂ K M cost) (first.1.value, rest.1.value, ())
      pure (⟨copied.value, first.1.steps + rest.1.steps + copied.steps + capacity i + 19⟩, rest.2)) := by
  rw [generateCode]
  generalize familyBlock state i = block
  generalize generateCode state capacity is = tail
  simp only [Program.run, Args.run, Expr.run, Var.get, Var.depth,
    StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
  congr 1
  funext first
  congr 1
  funext rest
  apply congrArg pure
  apply Prod.ext
  · apply congrArg (Run.mk _)
    omega
  · rfl

theorem generateCode_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (state : Ty CryptoAtom) (capacity : Family → Nat) (is : List Family)
    (s : state.Value (cryptoBase F G₁ G₂ K M))
    (out : Run (List (TapeCell F)) × state.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((generateCode state capacity is).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling state) ()).run s)) :
    out.1.steps ≤ generatePrice cost sampling capacity is ∧
      out.1.value.length = seedLength capacity is ∧ out.2 = s := by
  induction is generalizing s out with
  | nil =>
      simp only [generateCode, Program.run, Expr.run, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hout
      subst out
      exact ⟨le_rfl, rfl, rfl⟩
  | cons i is ih =>
      rw [generateCode_cons_run] at hout
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      obtain ⟨first, hf, rest, hr, rfl⟩ := hout
      have hb := familyBlock_bound cost sampling state i (capacity i) s first hf
      have ht := ih first.2 rest hr
      have ha := appendCode_steps (cell := Replay.Mixed.event) (arithmetic F G₁ G₂ K M cost)
        first.1.value rest.1.value
      refine ⟨?_, ?_, ht.2.2.trans hb.2.2⟩
      · dsimp [generatePrice]
        rw [hb.2.1] at ha
        nlinarith [hb.1, ht.1]
      · simp only [Expr.run_value]
        rw [appendCode_denote, List.length_append, hb.2.1, ht.2.1]
        rfl

theorem generateCode_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (state : Ty CryptoAtom) (capacity : Family → Nat) (is : List Family)
    (s : state.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => (p.1.value, p.2)) <$>
        ((generateCode state capacity is).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling state) ()).run s =
      (fun xs => (xs, s)) <$> generate (F := F) capacity is := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
      rw [generateCode_cons_run]
      simp only [map_bind, map_pure, Expr.run_value]
      simp_rw [appendCode_denote (cell := Replay.Mixed.event) (arithmetic F G₁ G₂ K M cost)]
      calc
        _ = (((familyBlock state i).run (arithmetic F G₁ G₂ K M cost)
              (Machine.effects sampling state) (capacity i, ())).run s >>= fun first =>
            (fun rest => (first.1.value ++ rest, first.2)) <$> generate (F := F) capacity is) := by
          congr 1
          funext first
          have h := congrArg (Functor.map
            (fun p : List (TapeCell F) × state.Value (cryptoBase F G₁ G₂ K M) =>
              (first.1.value ++ p.1, p.2))) (ih first.2)
          simpa only [Functor.map_map, bind_pure_comp] using h
        _ = _ := by
          have h := congrArg (fun action : ProbComp
              (List (TapeCell F) × state.Value (cryptoBase F G₁ G₂ K M)) =>
            action >>= fun first => (fun rest => (first.1 ++ rest, first.2)) <$>
              generate (F := F) capacity is)
            (familyBlock_erase cost sampling state i (capacity i) s)
          simpa only [bind_map_left, generate, map_bind, map_pure, bind_pure_comp,
            Functor.map_map] using h

/-- Actual machine execution produces the reference seed and preserves its store. -/
theorem generateCode_seed (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (state : Ty CryptoAtom) (capacity : Family → Nat) (is : List Family)
    (s : state.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => (toSeed p.1.value, p.2)) <$>
        ((generateCode state capacity is).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling state) ()).run s =
      (fun seed => (seed, s)) <$> generateSeed (replaySpec F) capacity is := by
  have h := congrArg (Functor.map (fun p => (toSeed p.1, p.2)))
    (generateCode_erase cost sampling state capacity is s)
  rw [← toSeed_generate]
  simpa only [Functor.map_map] using h

end Signatures.Runtime.Schnorr.SeedTape
