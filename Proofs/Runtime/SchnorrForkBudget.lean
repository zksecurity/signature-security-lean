import Proofs.Runtime.SchnorrForkMachine

/-! Source-derived bounds for the two-pass replay controller. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

theorem scalarReplayPrice_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {a b : Nat} (h : a ≤ b) : scalarReplayPrice cost sampling a ≤ scalarReplayPrice cost sampling b := by
  dsimp [scalarReplayPrice, Replay.Mixed.drawBound]
  nlinarith

theorem uniformReplayPrice_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {a b : Nat} (h : a ≤ b) (n : Nat) :
    uniformReplayPrice cost sampling a n ≤ uniformReplayPrice cost sampling b n := by
  dsimp [uniformReplayPrice, Replay.Mixed.drawBound]
  nlinarith

theorem replayPrices_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound : Nat) {a b : Nat} (h : a ≤ b) (k : Fin 3) :
    replayPrices cost sampling randomBound a k ≤ replayPrices cost sampling randomBound b k := by
  have hs := scalarReplayPrice_mono cost sampling h
  unfold replayPrices
  split
  · apply Nat.add_le_add_right
    exact Finset.sup_mono_fun fun n _ => uniformReplayPrice_mono cost sampling h n.val
  · split <;> omega

theorem passPrice_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) {a b : Nat} (h : a ≤ b) :
    passPrice cost sampling randomBound a localTime queries ≤
      passPrice cost sampling randomBound b localTime queries := by
  have hs := scalarReplayPrice_mono cost sampling h
  have hq : (∑ k, queries k * replayPrices cost sampling randomBound a k) ≤
      ∑ k, queries k * replayPrices cost sampling randomBound b k :=
    Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (replayPrices_mono cost sampling randomBound h k)
  dsimp [passPrice]
  omega

def eventBound (queries : Fin 3 → Nat) : Nat := (∑ k, queries k * eventAllowance k) + 1

def loggedPassPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  passPrice cost sampling randomBound (eventBound queries) localTime queries + 7 * eventBound queries + 28

def scanPrice (cost : PrimitiveCosts) (queries : Fin 3 → Nat) : Nat :=
  eventBound queries * (4 * cost.natOp + 70) + cost.field + 40

def selectPrice (cost : PrimitiveCosts) (queries : Fin 3 → Nat) : Nat :=
  selectionBound cost ((∑ k, queries k) + 1)

def secondPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  loggedPassPrice cost sampling randomBound localTime queries + selectPrice cost queries +
    scanPrice cost queries + finishPrice cost sampling + 124

def firstPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  selectPrice cost queries + scanPrice cost queries +
    secondPrice cost sampling randomBound localTime queries + sampling.scalar + 73

def forkPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  loggedPassPrice cost sampling randomBound localTime queries +
    firstPrice cost sampling randomBound localTime queries + 52

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

omit [SampleableType F] in
theorem scanCode_size (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    let r := scanCode.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())
    r.value.2.2.1 = r.value.2.2.2.length ∧ r.value.2.2.2.length ≤ xs.length := by
  simp only [Expr.run_value, scanCode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    List.length_reverse]
  have h := scanStep_size xs (n, false, (0 : F), 0, []) rfl
  exact ⟨h.1, by simpa only [Nat.zero_add, h.1] using h.2⟩

omit [SampleableType F] in
theorem selectionRun_budget (cost : PrimitiveCosts)
    (p : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (qH : Nat) (queries : Fin 3 → Nat)
    (hc : cacheSize p.2.1 ≤ (∑ k, queries k) + 1) :
    (selectionRun cost p qH).steps ≤ selectPrice cost queries := by
  have h := selectionRun_bound cost p qH
  have hl : p.2.1.2.2.length ≤ (∑ k, queries k) + 1 := by
    dsimp [cacheSize] at hc
    omega
  dsimp [selectionBound, selectPrice] at h ⊢
  nlinarith

theorem secondStage_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ : Bool × Nat)
    (scan₁ : scanResult.Value (cryptoBase F G₁ G₂ K M))
    (hlen : scan₁.2.2.2.length ≤ eventBound queries)
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run F × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((secondStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, choice₁, scan₁, pk, g, qH, data, ())).run s)) :
    out.1.steps ≤ secondPrice cost sampling randomBound localTime queries := by
  rw [secondStage_run] at hout
  simp only [mem_support_bind_iff] at hout
  obtain ⟨second, hs, choice₂, hc, result, hr, hout⟩ := hout
  rw [selectionRun_eq] at hc
  simp only [support_pure, Set.mem_singleton_iff] at hc hout
  subst choice₂
  subst out
  have hp := loggedPassProgram_bound cost sampling randomBound source (pk, data, ())
    localTime queries hsource g pk 0 scan₁.2.2.1 scan₁.2.2.2 second hs
  have hm := passPrice_mono cost sampling randomBound localTime queries hlen
  have hpass : second.1.steps ≤ loggedPassPrice cost sampling randomBound localTime queries := by
    dsimp [loggedPassPrice, eventBound] at *
    omega
  have hchoice := selectionRun_budget cost second.1.value qH queries hp.2.2.1
  have hscan := scanCode_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost choice₁.2 second.1.value.2.2
  have hscan' : (scanCode.run (arithmetic F G₁ G₂ K M cost)
      (choice₁.2, second.1.value.2.2, ())).steps ≤ scanPrice cost queries := by
    have he := hp.2.2.2
    dsimp [scanPrice, eventBound]
    nlinarith
  have hf := finishFork_bound cost sampling first second.1.value choice₁
    (selectionRun cost second.1.value qH).value scan₁ _ second.2 result hr
  dsimp [secondPrice]
  omega

theorem firstStage_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M))
    (hcache : cacheSize first.2.1 ≤ (∑ k, queries k) + 1)
    (hevents : first.2.2.length ≤ eventBound queries)
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run F × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((firstStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, pk, g, qH, data, ())).run s)) :
    out.1.steps ≤ firstPrice cost sampling randomBound localTime queries := by
  rw [firstStage_run, selectionRun_eq] at hout
  simp only [pure_bind] at hout
  have hc := selectionRun_budget cost first qH queries hcache
  have hs := scanCode_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost (selectionRun cost first qH).value.2 first.2.2
  have hs' : (scanCode.run (arithmetic F G₁ G₂ K M cost)
      ((selectionRun cost first qH).value.2, first.2.2, ())).steps ≤ scanPrice cost queries := by
    dsimp [scanPrice]
    nlinarith
  split at hout
  · split at hout
    · simp only [support_map, Set.mem_image] at hout
      obtain ⟨result, hr, rfl⟩ := hout
      have hlen := scanCode_size (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
        cost (selectionRun cost first qH).value.2 first.2.2
      have hb := secondStage_bound cost sampling randomBound source pk g qH data localTime queries
        hsource first (selectionRun cost first qH).value _ (hlen.2.trans hevents) s result hr
      dsimp [firstPrice]
      omega
    · simp only [support_map, Set.mem_image] at hout
      obtain ⟨x, _, rfl⟩ := hout
      dsimp [firstPrice]
      omega
  · simp only [support_map, Set.mem_image] at hout
    obtain ⟨x, _, rfl⟩ := hout
    dsimp [firstPrice]
    omega

/-- Every path through the complete machine is bounded using only the original
source program's budget. No runtime premise is imposed on the finished solver. -/
theorem forkCode_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (out : Run F)
    (hout : out ∈ support ((forkCode randomBound source).run cost sampling (pk, g, qH, data, ()))) :
    out.steps ≤ forkPrice cost sampling randomBound localTime queries := by
  rw [forkCode_run] at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨first, hf, result, hr, rfl⟩ := hout
  have hp := loggedPassProgram_bound cost sampling randomBound source (pk, data, ())
    localTime queries hsource g pk 0 0 [] first hf
  have hm := passPrice_mono cost sampling randomBound localTime queries (Nat.zero_le (eventBound queries))
  have hpass : first.1.steps ≤ loggedPassPrice cost sampling randomBound localTime queries := by
    dsimp [loggedPassPrice, eventBound] at *
    omega
  have hs := firstStage_bound cost sampling randomBound source pk g qH data localTime queries
    hsource first.1.value hp.2.2.1 hp.2.2.2 first.2 result hr
  dsimp [forkPrice]
  omega

/-- The only external input is the DLog challenge. Fixed generator, query limit and
adversary data are loaded by the general machine package, with their full load cost. -/
def forkPackage {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Machine.Package (cryptoBase F G₁ G₂ K M) [point₁] scalar where
  dataTypes := [point₁, .nat, dataTy]
  data := (g, qH, data, ())
  code := forkCode randomBound source

theorem forkPackage_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source (pk, data, ()) localTime queries)
    (out : Run F)
    (hout : out ∈ support ((forkPackage randomBound source g qH data).run cost sampling (pk, ()))) :
    out.steps ≤ forkPrice cost sampling randomBound localTime queries +
      (Env.load (base := cryptoBase F G₁ G₂ K M) (Γ := [point₁, .nat, dataTy]) (g, qH, data, ())).steps + 3 := by
  rw [Machine.Package.run_eq] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have h := forkCode_bound cost sampling randomBound source pk g qH data localTime queries hsource r hr
  dsimp [forkPackage]
  omega

end Signatures.Runtime.Schnorr
