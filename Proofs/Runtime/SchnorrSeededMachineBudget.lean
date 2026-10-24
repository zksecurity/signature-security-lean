import Proofs.Runtime.SchnorrSeededMachine

/-! Every path of the complete seeded controller is bounded from the original
source budget, including generation, both passes, reset, selection and fallback. -/

open OracleComp

namespace Signatures.Runtime.Schnorr.SeedTape

theorem sourcePrices_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound : Nat) {a b : Nat} (h : a ≤ b) (k : Fin 3) :
    sourcePrices cost sampling randomBound a k ≤ sourcePrices cost sampling randomBound b k := by
  have hs := scalarPrice_mono cost sampling h
  unfold sourcePrices
  split
  · apply Nat.add_le_add_right
    exact Finset.sup_mono_fun fun n _ => uniformPrice_mono cost sampling n.val h
  · split <;> omega

theorem passPrice_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) {a b : Nat} (h : a ≤ b) :
    passPrice cost sampling randomBound a localTime queries ≤
      passPrice cost sampling randomBound b localTime queries := by
  have hs := scalarPrice_mono cost sampling h
  have hq : (∑ k, queries k * sourcePrices cost sampling randomBound a k) ≤
      ∑ k, queries k * sourcePrices cost sampling randomBound b k :=
    Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (sourcePrices_mono cost sampling randomBound h k)
  dsimp [passPrice]
  omega

def finishPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) : Nat :=
  2 * cost.field + cost.division + cost.natOp + cost.scalarEq + cost.point₁Eq + sampling.scalar + 100

def secondPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qH randomBound length localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  length * (3 * cost.natOp + 80) + 100 +
    passPrice cost sampling randomBound (length + 1) localTime queries + 39 +
    selectPrice cost queries + finishPrice cost sampling + qH + 87

def firstPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qH randomBound length localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  selectPrice cost queries + length * (4 * cost.natOp + 70) + cost.field + 40 +
    cost.scalarEq + 10 + 2 * sampling.scalar +
    secondPrice cost sampling qH randomBound length localTime queries + qH + 80

def forkPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (capacity : Family → Nat) (families : List Family)
    (qH randomBound localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  generatePrice cost sampling capacity families +
    passPrice cost sampling randomBound (seedLength capacity families) localTime queries + 39 +
    firstPrice cost sampling qH randomBound (seedLength capacity families) localTime queries + 57

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem finishFork_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (choice : Bool × Nat) (index : Nat)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run F × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((finishFork.run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (first, second, choice, index, ())).run s)) :
    out.1.steps ≤ finishPrice cost sampling ∧ out.2 = s := by
  rw [finishFork_run] at hout
  have hg := finishGuards_steps cost first second choice index
  have he : (extract.run (arithmetic F G₁ G₂ K M cost)
      (first.1.1.2.2, second.1.1.2.2, first.1.2, second.1.2, ())).steps =
        2 * cost.field + cost.division + 16 := by
    simp [extract, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
    omega
  dsimp only at hout
  split at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact ⟨by dsimp [finishPrice]; omega, rfl⟩
  · simp only [support_map, Set.mem_image] at hout
    obtain ⟨x, _, rfl⟩ := hout
    exact ⟨by dsimp [finishPrice]; omega, rfl⟩

theorem runWithTape_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (tape : List (TapeCell F)) (s : machineStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run (cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) ×
      machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((runWithTape randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (tape, pk, g, data, ())).run s)) :
    out.1.steps ≤ passPrice cost sampling randomBound tape.length localTime queries + 39 ∧
      out.1.value.2 = out.2.1 ∧ out.2.1.1 = (g, pk) ∧
      cacheSize out.1.value.2 ≤ (∑ k, queries k) + 1 := by
  rw [runWithTape_run, capturePass_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨a, ⟨p, hp, rfl⟩, rfl⟩ := hout
  have h := passCode_bound cost sampling randomBound source (pk, data, ())
    localTime queries hsource g pk tape p hp
  exact ⟨by dsimp; omega, rfl, h.2.1, h.2.2.1⟩

theorem secondStage_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (tape : List (TapeCell F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (index : Nat) (fresh : F) (s : machineStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run F × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((secondStage qH randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (tape, first, index, fresh, pk, g, data, ())).run s)) :
    out.1.steps ≤ secondPrice cost sampling qH randomBound tape.length localTime queries := by
  rw [secondStage_run] at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨second, hs, result, hr, rfl⟩ := hout
  have hp := runWithTape_bound cost sampling randomBound source pk g data localTime queries hsource _ s second hs
  have hreset := resetCode_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost 1 index tape (1, fresh, 0)
  have hlen : (resetCode.run (arithmetic F G₁ G₂ K M cost)
      (1, index, tape, (1, fresh, 0), ())).value.length ≤ tape.length + 1 := by
    rw [Expr.run_value, resetCode_denote]
    exact reset_length 1 index (1, fresh, 0) tape
  have hm := passPrice_mono cost sampling randomBound localTime queries hlen
  have hc := selectionRun_budget cost (second.1.value.1, second.1.value.2, []) qH queries hp.2.2.2
  have hf := finishFork_bound cost sampling first second.1.value
    (selectionRun cost (second.1.value.1, second.1.value.2, []) qH).value index second.2 result hr
  dsimp [secondPrice]
  omega

theorem firstStage_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (tape : List (TapeCell F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (hcache : cacheSize first.2 ≤ (∑ k, queries k) + 1)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run F × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((firstStage qH randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (tape, first, pk, g, data, ())).run s)) :
    out.1.steps ≤ firstPrice cost sampling qH randomBound tape.length localTime queries := by
  rw [firstStage_run] at hout
  dsimp only at hout
  have hc := selectionRun_budget cost (first.1, first.2, []) qH queries hcache
  have hs := scanCode_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost (selectionRun cost (first.1, first.2, []) qH).value.2 tape
  have hcheck : (if (scanCode.run (arithmetic F G₁ G₂ K M cost)
      ((selectionRun cost (first.1, first.2, []) qH).value.2, tape, ())).value.1
      then cost.scalarEq + 10 else 4) ≤ cost.scalarEq + 10 := by split <;> omega
  split at hout
  · simp only [mem_support_bind_iff] at hout
    obtain ⟨fresh, _, hout⟩ := hout
    split at hout
    · simp only [support_map, Set.mem_image] at hout
      obtain ⟨x, _, rfl⟩ := hout
      dsimp [firstPrice]
      omega
    · simp only [support_map, Set.mem_image] at hout
      obtain ⟨result, hr, rfl⟩ := hout
      have hb := secondStage_bound cost sampling qH randomBound source pk g data localTime queries
        hsource tape first (selectionRun cost (first.1, first.2, []) qH).value.2 fresh s result hr
      dsimp [firstPrice]
      omega
  · simp only [support_map, Set.mem_image] at hout
    obtain ⟨x, _, rfl⟩ := hout
    dsimp [firstPrice]
    omega

/-- Complete source-derived arithmetic cost; there is no runtime premise on
the completed reduction, and even failing or colliding runs are included. -/
theorem forkCode_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (capacity : Family → Nat) (families : List Family) (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (out : Run F)
    (hout : out ∈ support ((forkCode capacity families qH randomBound source).run
      cost sampling (pk, g, data, ()))) :
    out.steps ≤ forkPrice cost sampling capacity families qH randomBound localTime queries := by
  rw [forkCode_run] at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨seed, hg, first, hp, result, hr, rfl⟩ := hout
  have hgen := generateCode_bound cost sampling machineStore capacity families (((g, pk), [], []), []) seed hg
  have hpass := runWithTape_bound cost sampling randomBound source pk g data localTime queries
    hsource seed.1.value seed.2 first hp
  have hstage := firstStage_bound cost sampling qH randomBound source pk g data localTime queries
    hsource seed.1.value first.1.value hpass.2.2.2 first.2 result hr
  rw [hgen.2.1] at hpass hstage
  dsimp [forkPrice]
  omega

def forkPackage {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (localTime : Nat) (queries : Fin 3 → Nat)
    (g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Machine.Package (cryptoBase F G₁ G₂ K M) [point₁] scalar where
  dataTypes := [point₁, dataTy]
  data := (g, data, ())
  code := sourceForkCode qH randomBound source localTime queries

def packagePrice {dataTy} (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qH randomBound : Nat) (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (localTime : Nat) (queries : Fin 3 → Nat)
    (g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) : Nat :=
  forkPrice cost sampling (Seeded.budget source localTime queries qH) (sourceFamilies source)
    qH randomBound localTime queries +
    (Env.load (base := cryptoBase F G₁ G₂ K M) (Γ := [point₁, dataTy]) (g, data, ())).steps + 3

/-- Fixed data and the external input-register spine are also charged. -/
theorem forkPackage_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (out : Run F)
    (hout : out ∈ support ((forkPackage qH randomBound source localTime queries g data).run
      cost sampling (pk, ()))) :
    out.steps ≤ packagePrice cost sampling qH randomBound source localTime queries g data := by
  rw [Machine.Package.run_eq] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have h := forkCode_bound cost sampling (Seeded.budget source localTime queries qH)
    (sourceFamilies source) qH randomBound source pk g data localTime queries hsource r hr
  dsimp [packagePrice, forkPackage]
  omega

end Signatures.Runtime.Schnorr.SeedTape
