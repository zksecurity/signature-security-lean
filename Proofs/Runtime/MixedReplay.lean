import Proofs.Runtime.StoreProduct
import Proofs.Runtime.Index

/-! A first-order replay tape for mixed scalar and finite random choices. The query
code is retained in each event: 0 is private scalar, 1 is a live hash challenge, and
`n + 2` is a uniform `Fin (n + 1)` draw. Only valid recorded prefixes are used by the
fork driver; decoding is total even on malformed input tapes. -/

open OracleComp

namespace Signatures.Runtime.Replay.Mixed

abbrev event : Ty CryptoAtom := .pair .nat (.pair scalar .nat)
abbrev store : Ty CryptoAtom := .pair .nat (.pair .nat (.pair (.list event) (.list event)))

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c :=
  .var (.there (.there .here))

def emptyEvent {Γ} : Expr CryptoOp Γ event :=
  .pair (.nat 0) (.pair (.op .zero .unit) (.nat 0))

/-- Codecs are first-order expressions, not uncharged host callbacks. -/
def draw {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [event] a) (encode : Expr CryptoOp [a] event) :
    Program CryptoOp (Machine.Effect store) [.unit] a :=
  .bind (.query .read .unit)
    (.bind
      (.branch (.op .natLt (.pair (.fst v0) (.fst (.snd v0))))
        (.bind (.call (.ret (index CryptoOp.natEq CryptoOp.natSub))
          (.cons (.fst v0) (.cons emptyEvent
            (.cons (.fst (.snd (.snd v0))) .nil))))
          (.call (.ret decode) (.cons v0 .nil)))
        (.query sample .unit))
      (.bind (.call (.ret encode) (.cons v0 .nil))
        (.bind (.query .write
          (.pair (.op .natAdd (.pair (.fst v2) (.nat 1)))
            (.pair (.fst (.snd v2))
              (.pair (.fst (.snd (.snd v2)))
                (.cons v0 (.snd (.snd (.snd v2))))))))
          (.ret v2))))

def scalarDecode : Expr CryptoOp [event] scalar := .fst (.snd v0)
def scalarEncode (tag : Bool) : Expr CryptoOp [scalar] event :=
  .pair (.nat (if tag then 1 else 0)) (.pair v0 (.nat 0))

def uniformDecode (n : Nat) : Expr CryptoOp [event] (boundedNat n) :=
  .op (.finOfNat n) (.snd (.snd v0))
def uniformEncode (n : Nat) : Expr CryptoOp [boundedNat n] event :=
  .pair (.nat (n + 2)) (.pair (.op .zero .unit) (.op (.finVal n) v0))

def scalarDraw (tag : Bool) := draw .scalar scalarDecode (scalarEncode tag)
def uniformDraw (n : Nat) := draw (.uniform n) (uniformDecode n) (uniformEncode n)

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
    (readPrice writePrice : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [event] a) (encode : Expr CryptoOp [a] event)
    (cursor limit : Nat) (tape events : List (Nat × F × Nat)) (h : cursor < limit) :
    (((draw sample decode encode).run (arithmetic F G₁ G₂ K M cost)
      (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run
        (cursor, limit, tape, events)) =
      let get := (index (cell := event) CryptoOp.natEq CryptoOp.natSub).run
        (arithmetic F G₁ G₂ K M cost) (cursor, (0, (0 : F), 0), tape, ())
      let answer := decode.run (arithmetic F G₁ G₂ K M cost) (get.value, ())
      let encoded := encode.run (arithmetic F G₁ G₂ K M cost) (answer.value, ())
      pure (⟨answer.value, get.steps + answer.steps + encoded.steps +
        cost.field + 2 * cost.natOp + readPrice + writePrice + 81⟩,
        (cursor + 1, limit, tape, encoded.value :: events)) := by
  unfold draw
  generalize index (cell := event) CryptoOp.natEq CryptoOp.natSub = get
  dsimp [Program.run, Args.run, Expr.run, emptyEvent, v0, v1, v2, Var.get, Var.depth,
    StateT.run, StateT.bind, StateT.pure, Machine.pricedStoreEffects, arithmetic, CryptoOp.price]
  simp only [state_pure, pure_bind,
    show decide (cursor < limit) = true from by simp [h], ite_true]
  congr 1
  apply Prod.ext
  · apply congrArg (Run.mk _)
    omega
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem draw_miss (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [event] a) (encode : Expr CryptoOp [a] event)
    (random : ProbComp (a.Value (cryptoBase F G₁ G₂ K M))) (price : Nat)
    (hsample : ∀ s, (Machine.pricedStoreEffects sampling store readPrice writePrice sample ()).run s =
      (fun x => (⟨x, price⟩, s)) <$> random)
    (cursor limit : Nat) (tape events : List (Nat × F × Nat)) (h : ¬ cursor < limit) :
    (((draw sample decode encode).run (arithmetic F G₁ G₂ K M cost)
      (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run
        (cursor, limit, tape, events)) =
      (fun answer =>
        let encoded := encode.run (arithmetic F G₁ G₂ K M cost) (answer, ())
        (⟨answer, price + encoded.steps + 2 * cost.natOp + readPrice + writePrice + 57⟩,
          (cursor + 1, limit, tape, encoded.value :: events))) <$> random := by
  unfold draw
  dsimp [Program.run, Args.run, Expr.run, emptyEvent, v0, v1, v2, Var.get, Var.depth]
  generalize Machine.pricedStoreEffects (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    sampling store readPrice writePrice sample () = action at hsample ⊢
  dsimp [StateT.run, StateT.bind, StateT.pure, Machine.pricedStoreEffects,
    arithmetic, CryptoOp.price] at hsample ⊢
  simp only [state_bind, state_pure, pure_bind,
    show decide (cursor < limit) = false from by simp [h], Bool.false_eq_true, ite_false]
  rw [hsample]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  congr 1
  funext answer
  congr 1
  apply Prod.ext
  · apply congrArg (Run.mk _)
    omega
  · rfl

/-- The bound includes scanning, codec execution and all store updates. -/
def drawBound (cost : PrimitiveCosts) (price cDecode cEncode length : Nat)
    (readPrice : Nat := 1) (writePrice : Nat := 1) : Nat :=
  length * (2 * cost.natOp + 26) + price + cDecode + cEncode +
    cost.field + 2 * cost.natOp + readPrice + writePrice + 94

theorem draw_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [event] a) (encode : Expr CryptoOp [a] event)
    (random : ProbComp (a.Value (cryptoBase F G₁ G₂ K M))) (price cDecode cEncode : Nat)
    (hsample : ∀ s, (Machine.pricedStoreEffects sampling store readPrice writePrice sample ()).run s =
      (fun x => (⟨x, price⟩, s)) <$> random)
    (hdecode : ∀ cell, (decode.run (arithmetic F G₁ G₂ K M cost) (cell, ())).steps ≤ cDecode)
    (hencode : ∀ value, (encode.run (arithmetic F G₁ G₂ K M cost) (value, ())).steps ≤ cEncode)
    (cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) × store.Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((draw sample decode encode).run (arithmetic F G₁ G₂ K M cost)
      (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run
        (cursor, limit, tape, events))) :
    z.1.steps ≤ drawBound cost price cDecode cEncode tape.length readPrice writePrice ∧
      z.2 = (cursor + 1, limit, tape,
        (encode.run (arithmetic F G₁ G₂ K M cost) (z.1.value, ())).value :: events) := by
  by_cases h : cursor < limit
  · rw [draw_hit cost sampling readPrice writePrice sample decode encode cursor limit tape events h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst z
    have hi := index_steps_le (cell := event) (arithmetic F G₁ G₂ K M cost)
      CryptoOp.natEq CryptoOp.natSub cost.natOp (by intros; rfl) (by intros; rfl)
      cursor (0, (0 : F), 0) tape
    have hd := hdecode ((index (cell := event) CryptoOp.natEq CryptoOp.natSub).run
      (arithmetic F G₁ G₂ K M cost) (cursor, (0, (0 : F), 0), tape, ())).value
    have he := hencode (decode.run (arithmetic F G₁ G₂ K M cost)
      (((index (cell := event) CryptoOp.natEq CryptoOp.natSub).run
        (arithmetic F G₁ G₂ K M cost) (cursor, (0, (0 : F), 0), tape, ())).value, ())).value
    exact ⟨by dsimp [drawBound]; omega, rfl⟩
  · rw [draw_miss cost sampling readPrice writePrice sample decode encode random price hsample
      cursor limit tape events h] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨answer, _, rfl⟩ := hz
    have he := hencode answer
    exact ⟨by dsimp [drawBound]; omega, rfl⟩

theorem draw_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (readPrice writePrice : Nat)
    {a : Ty CryptoAtom} (sample : Machine.Effect store .unit a)
    (decode : Expr CryptoOp [event] a) (encode : Expr CryptoOp [a] event)
    (random : ProbComp (a.Value (cryptoBase F G₁ G₂ K M))) (price : Nat)
    (hsample : ∀ s, (Machine.pricedStoreEffects sampling store readPrice writePrice sample ()).run s =
      (fun x => (⟨x, price⟩, s)) <$> random)
    (cursor limit : Nat) (tape events : List (Nat × F × Nat)) :
    (fun z => (z.1.value, z.2)) <$>
      (((draw sample decode encode).run (arithmetic F G₁ G₂ K M cost)
        (Machine.pricedStoreEffects sampling store readPrice writePrice) ((), ())).run
          (cursor, limit, tape, events)) =
      (fun answer => (answer, (cursor + 1, limit, tape,
        encode.denote (arithmetic F G₁ G₂ K M cost) (answer, ()) :: events))) <$>
        (if cursor < limit then
          pure (decode.denote (arithmetic F G₁ G₂ K M cost)
            ((tape[cursor]?).getD (0, (0 : F), 0), ()))
        else random) := by
  by_cases h : cursor < limit
  · rw [draw_hit cost sampling readPrice writePrice sample decode encode cursor limit tape events h]
    have hi := index_denote (cell := event) (arithmetic F G₁ G₂ K M cost)
      CryptoOp.natEq CryptoOp.natSub (by intros; rfl) (by intros; rfl)
      cursor (0, (0 : F), 0) tape
    simp only [h, ite_true, map_pure, Expr.run_value, hi]
  · rw [draw_miss cost sampling readPrice writePrice sample decode encode random price hsample
      cursor limit tape events h]
    simp only [h, ite_false, Functor.map_map, Expr.run_value]

omit [SampleableType F] in
theorem scalarDecode_denote (cost : PrimitiveCosts) (cell : Nat × F × Nat) :
    scalarDecode.denote (arithmetic F G₁ G₂ K M cost) (cell, ()) = cell.2.1 := rfl

omit [SampleableType F] in
theorem scalarEncode_denote (cost : PrimitiveCosts) (tag : Bool) (value : F) :
    (scalarEncode tag).denote (arithmetic F G₁ G₂ K M cost) (value, ()) =
      ((if tag then 1 else 0), value, 0) := rfl

omit [SampleableType F] in
theorem uniformDecode_denote (cost : PrimitiveCosts) (n : Nat) (cell : Nat × F × Nat) :
    (uniformDecode n).denote (arithmetic F G₁ G₂ K M cost) (cell, ()) =
      (⟨cell.2.2 % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩ : Fin (n + 1)) := rfl

omit [SampleableType F] in
theorem uniformEncode_denote (cost : PrimitiveCosts) (n : Nat) (value : Fin (n + 1)) :
    (uniformEncode n).denote (arithmetic F G₁ G₂ K M cost) (value, ()) =
      (n + 2, 0, value.val) := rfl

omit [SampleableType F] in
theorem scalarDecode_steps (cost : PrimitiveCosts) (cell : Nat × F × Nat) :
    (scalarDecode.run (arithmetic F G₁ G₂ K M cost) (cell, ())).steps = 3 := rfl

omit [SampleableType F] in
theorem scalarEncode_steps (cost : PrimitiveCosts) (tag : Bool) (value : F) :
    ((scalarEncode tag).run (arithmetic F G₁ G₂ K M cost) (value, ())).steps ≤ 6 := by
  cases tag <;> simp [scalarEncode, Expr.run, v0, Var.get, Var.depth]

omit [SampleableType F] in
theorem uniformDecode_steps (cost : PrimitiveCosts) (n : Nat) (cell : Nat × F × Nat) :
    ((uniformDecode n).run (arithmetic F G₁ G₂ K M cost) (cell, ())).steps =
      cost.natOp + 4 := by
  simp [uniformDecode, Expr.run, v0, Var.get, Var.depth, arithmetic, CryptoOp.price]
  omega

omit [SampleableType F] in
theorem uniformEncode_steps (cost : PrimitiveCosts) (n : Nat) (value : Fin (n + 1)) :
    ((uniformEncode n).run (arithmetic F G₁ G₂ K M cost) (value, ())).steps =
      n + cost.field + cost.natOp + 9 := by
  simp [uniformEncode, Expr.run, v0, Var.get, Var.depth, arithmetic, CryptoOp.price]
  omega

omit [SampleableType F] in
theorem uniformCodec_roundtrip (cost : PrimitiveCosts) (n : Nat) (value : Fin (n + 1)) :
    (uniformDecode n).denote (arithmetic F G₁ G₂ K M cost)
      ((uniformEncode n).denote (arithmetic F G₁ G₂ K M cost) (value, ()), ()) = value := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt value.isLt

theorem scalarDraw_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (tag : Bool) (cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (z : Run F × store.Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((scalarDraw tag).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling store) ((), ())).run (cursor, limit, tape, events))) :
    z.1.steps ≤ drawBound cost sampling.scalar 3 6 tape.length ∧
      z.2 = (cursor + 1, limit, tape, ((if tag then 1 else 0), z.1.value, 0) :: events) := by
  exact draw_bound cost sampling 1 1 .scalar scalarDecode (scalarEncode tag)
    ($ᵗ F) sampling.scalar 3 6 (fun _ => rfl)
    (fun _ => le_of_eq (scalarDecode_steps cost _)) (scalarEncode_steps cost tag)
    cursor limit tape events z hz

theorem uniformDraw_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (n cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (z : Run (Fin (n + 1)) × store.Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((uniformDraw n).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling store) ((), ())).run (cursor, limit, tape, events))) :
    z.1.steps ≤ drawBound cost (sampling.uniform n) (cost.natOp + 4)
        (n + cost.field + cost.natOp + 9) tape.length ∧
      z.2 = (cursor + 1, limit, tape, (n + 2, 0, z.1.value.val) :: events) := by
  exact draw_bound cost sampling 1 1 (.uniform n) (uniformDecode n) (uniformEncode n)
    (liftM (unifSpec.query n)) (sampling.uniform n)
    (cost.natOp + 4) (n + cost.field + cost.natOp + 9) (fun _ => rfl)
    (fun _ => le_of_eq (uniformDecode_steps cost n _))
    (fun _ => le_of_eq (uniformEncode_steps cost n _)) cursor limit tape events z hz

end Signatures.Runtime.Replay.Mixed
