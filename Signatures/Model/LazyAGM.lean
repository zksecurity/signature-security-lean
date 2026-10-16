import Signatures.Model.SignatureInteraction

/-!
# Query-only algebraic signature game

The adversary receives only the verification key. Base queries, signing, and final verification
share one lazy random oracle. Only answers explicitly returned to the adversary enter its
representation transcript; internal signing/verification base lookups do not.
The source experiment executes a certified adversary through `AlgebraicGroupModel.Interaction`.
`SignatureInteraction` supplies the signature adapter and its exact execution-equivalence proof.
Grouped transcripts remain a proof-side view for the existing reductions.
-/

open OracleComp OracleSpec

namespace Model.LazyAGM

variable {F ι M G₁ G₂ : Type}

/-- A table is hidden inside the simulator, never passed to `A.main`. -/
-- Proof/reduction-side handler, not the lazy source oracle: H and signO are already fixed.
def fixedImpl (H : ι → G₁) (signO : M → G₁) :
    -- Record only explicit base/signing replies while retaining probabilistic private coins.
    QueryImpl (advSpec ι M G₁) (StateT (Transcript ι M G₁) ProbComp) :=
  -- Private-randomness queries still sample normally.
  handler (fun n => (unifSpec.query n : ProbComp (Fin (n + 1))))
    -- Base and signing queries read their supplied functions, with no fresh sampling here.
    (fun i => pure (H i)) (fun m => pure (signO m))

-- Execute that proof-side simulation with the adversary's public key and private oracle data.
def fixedRun (A : Adversary F ι M G₁ G₂) (pk : G₂) (H : ι → G₁) (signO : M → G₁) :
    -- Return the forgery coefficients together with the two visible-reply transcripts.
    ProbComp (Output F M × Transcript ι M G₁) :=
  -- Start both transcripts empty; this is not an initialization of the source hash cache.
  (simulateQ (fixedImpl H signO) (A.main pk)).run ([], [])

/-- Aggregate coefficients only at indices actually returned by explicit base queries. -/
def baseCoeff [AddCommMonoid F] [DecidableEq ι]
    (coeff : List F) (tr : List (ι × G₁)) (i : ι) : F :=
  (tr.mapIdx fun n p => if p.1 = i then tokenCoeff coeff n else 0).sum

section Reductions

variable [Field F] [SampleableType F] [Fintype ι] [DecidableEq ι]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

def denominatorCoeff (w : ι → M → F) (out : Output F M) (tr : Transcript ι M G₁)
    (i : ι) : F :=
  w i out.mstar - (tr.2.mapIdx fun n q => tokenCoeff out.ξ n * w i q.1).sum

/-- Explicit good-branch reduction. Tables are private simulator randomness, not public inputs. -/
noncomputable def goodReduction (w : ι → M → F) (A : Adversary F ι M G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g₁ X₁ _ X₂ => do
  let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let (out, tr) ← fixedRun A X₂ (fun i => ρ i • g₁)
    (fun m => (∑ i, ρ i * w i m) • X₁)
  let const := out.β + ∑ i, baseCoeff out.γ tr.1 i * ρ i
  let lin := (tr.2.mapIdx fun n q => tokenCoeff out.ξ n * (∑ i, ρ i * w i q.1)).sum
  pure (const / ((∑ i, ρ i * w i out.mstar) - lin))

/-- Explicit zero-denominator reduction, with independently masked affine bases. -/
noncomputable def badReduction (w : ι → M → F) (A : Adversary F ι M G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g₁ X₁ g₂ _ => do
  let κ ← ($ᵗ F : ProbComp F)
  let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let b ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let H := fun i => a i • X₁ + b i • g₁
  let (out, tr) ← fixedRun A (κ • g₂) H (fun m => κ • ∑ i, w i m • H i)
  pure (-(∑ i, denominatorCoeff w out tr i * b i) /
    (∑ i, denominatorCoeff w out tr i * a i))

end Reductions

section Game

-- The source game needs scalar sampling, but no finite enumeration of the base-index type.
variable [Field F] [SampleableType F]
  -- Hash replies are sampled in G1; signing combines and scales these points.
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  -- A verification key is a scalar multiple of a G2 point.
  [AddCommGroup G₂] [Module F G₂]

-- A scheme gives each message a finite list of base indices and scalar weights.
def signing (terms : M → List (ι × F)) (α : F) (m : M) :
    -- Signing can use randomness/base queries and ultimately returns a G1 point.
    OracleComp (baseSpec ι G₁) G₁ := do
  -- Compute the weighted base sum using the same cache as the adversary's explicit queries.
  let H ← evalTerms (terms m)
  -- Multiply by the secret scalar; internal base lookups are not explicit adversary replies.
  pure (α • H)

/-- Grouped-transcript proof view, related to actual execution by `interactiveRun_eq`. -/
-- This alternative view records separate hash and signing transcripts for the proofs.
def run (terms : M → List (ι × F)) (α : F)
    -- The adversary gets pk, while the signer privately uses alpha.
    (A : Adversary F ι M G₁ G₂) (pk : G₂) :
    -- Return A's coefficient output with the visible replies; base-oracle calls remain open.
    OracleComp (baseSpec ι G₁) (Output F M × Transcript ι M G₁) :=
  -- Interpret A's three query variants through the transcript-recording handler.
  (simulateQ (handler
    -- Forward private randomness to the left component of the ambient oracle interface.
    (fun n => (liftM ((baseSpec ι G₁).query (.inl n)) : OracleComp (baseSpec ι G₁) _))
    -- Forward explicit base requests to the right component; the handler records their replies.
    (fun i => (liftM ((baseSpec ι G₁).query (.inr i)) : OracleComp (baseSpec ι G₁) G₁))
    -- Answer signing requests with the secret-key signer; both visible transcripts start empty.
    (signing terms α)) (A.main pk)).run ([], [])

/-- Actual source-game execution uses the generic certified interactive adversary. -/
-- This is the certified AGM execution path actually used by the source experiment.
def interactiveRun (terms : M → List (ι × F)) (α : F)
    -- Supply the adversary, its signature-group generator input, and its verification key.
    (A : Adversary F ι M G₁ G₂) (g₁ : G₁) (pk : G₂) :
    -- The remaining external interface provides private randomness and lazy base values.
    OracleComp (baseSpec ι G₁)
      -- Return plain result data and separately typed group lists, after certified execution.
      (AlgebraicGroupModel.Interaction.Message (Interactive.Result F M) (Interactive.Group G₁ G₂)) :=
  -- Run A's certified adapter, then project away final coefficients and accumulated basis.
  (fun z => z.1.value) <$> A.toInteractive.run (Interactive.impl
    -- Private randomness stays an ambient uniform query; it adds no group inputs.
    (fun n => (liftM ((baseSpec ι G₁).query (.inl n)) : OracleComp (baseSpec ι G₁) _))
    -- Explicit base queries receive G1 points from the ambient base oracle.
    (fun i => (liftM ((baseSpec ι G₁).query (.inr i)) : OracleComp (baseSpec ι G₁) G₁))
    -- Install the signer and initialize the tracked groups with [g1] and [pk], respectively.
    (signing terms α)) (Interactive.initialInput g₁ pk)

omit [SampleableType F] [SampleableType G₁] in
/-- The old grouped-transcript runner remains an exact proof-side view of the source game. -/
theorem interactiveRun_eq (terms : M → List (ι × F)) (α : F)
    (A : Adversary F ι M G₁ G₂) (g₁ : G₁) (pk : G₂) :
    interactiveRun terms α A g₁ pk = Interactive.observe g₁ <$> run terms α A pk :=
  A.toInteractive_run _ _ _ g₁ pk

/-- A game-level condition such as OOPS's distinct-message limit on the final target topic. -/
-- Add the target-group operations needed for the mathematical signature-verification check.
noncomputable def experiment {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ]
    -- Pairing connects signature points in G1 with keys in G2.
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    -- terms specifies the scheme; admissible may impose an additional transcript condition.
    (terms : M → List (ι × F)) (admissible : M → List M → Prop)
    -- The game fixes its base points and adversary before sampling the secret key.
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F ι M G₁ G₂) :
    -- This experiment returns a win bit but still needs its base/randomness oracle interpreted.
    OracleComp (baseSpec ι G₁) Bool := by
  -- Obtain decidability for the winning predicate; this is not an efficient verifier claim.
  classical
  -- Construct the oracle program implementing key generation, interaction, and verification.
  exact do
    -- Sample the secret scalar uniformly, including zero; nonzero sampling is not assumed.
    let α ← (liftM ($ᵗ F) : OracleComp (baseSpec ι G₁) F)
    -- Give A the verification key alpha*g2 and run its adaptive queries through the adapter.
    let result ← interactiveRun terms α A g₁ (α • g₂)
    -- Read metadata from data, but take the candidate signature only from the tracked G1 list.
    match result.data, result.groups .signature with
    -- Accept this shape only: an output plus the actual signed-message log, and one G1 point.
    | some (out, signed), [σ] =>
        -- Final verification queries the same base oracle, sampling unseen indices on demand.
        let target ← evalTerms (terms out.mstar)
        -- First require the scheme-specific condition, such as OOPS's target-topic degree bound.
        pure (decide (admissible out.mstar signed ∧
          -- The left pairing uses the supplied signature, not a point decoded from ordinary data.
          BilinearGroup.pairing (F := F) (Gₜ := Gₜ) σ g₂ =
            -- It must equal the pairing of the message's weighted base sum with the public key.
            BilinearGroup.pairing (F := F) (Gₜ := Gₜ) target (α • g₂) ∧
          -- Finally require exact-message freshness; for OOPS/Proximity M includes topic/slot.
          out.mstar ∉ signed))
    -- Adapter rejection, missing metadata, or any other G1-list length cannot win.
    | _, _ => pure false

omit [SampleableType G₁] in
/-- Integration preserves the original game computation, not just its success probability. -/
theorem experiment_eq {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    (terms : M → List (ι × F)) (admissible : M → List M → Prop)
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F ι M G₁ G₂) :
    experiment (Gₜ := Gₜ) terms admissible g₁ g₂ A = (by
  classical
  exact do
    let α ← (liftM ($ᵗ F) : OracleComp (baseSpec ι G₁) F)
    let (out, tr) ← run terms α A (α • g₂)
    let σ := materialize g₁ out tr
    let target ← evalTerms (terms out.mstar)
    pure (decide (admissible out.mstar (tr.2.map Prod.fst) ∧
      BilinearGroup.pairing (F := F) (Gₜ := Gₜ) σ g₂ =
        BilinearGroup.pairing (F := F) (Gₜ := Gₜ) target (α • g₂) ∧
      out.mstar ∉ tr.2.map Prod.fst))) := by
  classical
  simp only [experiment, interactiveRun_eq, bind_map_left, Interactive.observe,
    Interactive.groupLists]

/-- Uniform queries are forwarded; base queries sample once and cache persistently. -/
-- VCVio's randomOracle looks up the requested index in the cache:
-- a hit returns the saved point unchanged; a miss samples uniformly, saves it, and returns it.
-- This hidden cache is distinct from the AGM runner's received-point basis. Internal signing
-- and verification lookups populate the cache without exposing those base points to A.
-- An explicit repeated hash query reuses its cached point but supplies another reply occurrence.
-- Base-index equality is needed to recognize repeated queries to the same cached index.
noncomputable def lazyImpl [DecidableEq ι] :
    -- The hidden state is the base oracle's cache; replies are generated probabilistically.
    QueryImpl (baseSpec ι G₁) (StateT (ι →ₒ G₁).QueryCache ProbComp) :=
  -- Randomness bypasses the cache; a base index gets a fresh uniform G1 point only on first use.
  unifFwdImpl (ι →ₒ G₁) + randomOracle (spec := ι →ₒ G₁)

-- Close the source experiment by supplying its actual lazy random-oracle interpretation.
noncomputable def game {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ]
    -- Pairing is used for winning; index equality is used for the shared base cache.
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq ι]
    -- These two functions distinguish BLS, OOPS, and Proximity without changing the runner.
    (terms : M → List (ι × F)) (admissible : M → List M → Prop)
    -- A fully interpreted game is a probabilistic Boolean computation, not yet a probability.
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F ι M G₁ G₂) : ProbComp Bool :=
  -- Start one empty cache shared by all lookups; run' discards its final contents, not the win bit.
  (simulateQ lazyImpl (experiment (Gₜ := Gₜ) terms admissible g₁ g₂ A)).run' ∅

-- Turn the same experiment into a numerical success probability in extended nonnegative reals.
noncomputable def advantage {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ]
    -- Use exactly the pairing and cache requirements of game; no hardness premise is added.
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq ι]
    -- Keep the scheme's weighted bases and additional winning condition unchanged.
    (terms : M → List (ι × F)) (admissible : M → List M → Prop)
    -- Fix the same game parameters; ENNReal is the probability value's ambient type.
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F ι M G₁ G₂) : ENNReal :=
  -- Evaluate the game's distribution on the singleton event {true}.
  𝒟[game (Gₜ := Gₜ) terms admissible g₁ g₂ A] {true}

end Game

end Model.LazyAGM
