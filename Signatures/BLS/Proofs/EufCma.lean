import Signatures.BLS.Game
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility
import VCVio.EvalDist.Monad.Measure

/-! The readable BLS game `rom` and the standard EUF-CMA experiment `eufCma` have
the same distribution. `rom`'s oracle draws a hash exponent `ρ` and answers
`ρ • g₁`; the standard oracle draws the point itself. The two agree because `g₁`
generates (`curve.generates`), so the coupling is the bijection `ρ ↦ ρ • g₁`,
applied once per fresh hash through a state projection from the standard
oracle's cache and signing log onto the exponent table and signed set. -/

open OracleComp OracleSpec Model MeasureTheory

namespace BLS.Game

section Flatten
variable {ι ι' κ : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {logged : OracleSpec κ} {S α : Type}

/-- A logged handler into `spec'`, followed by a stateful implementation of `spec'`, as one
stateful handler whose state carries the accumulated log. -/
def flattened (so : QueryImpl spec (WriterT (QueryLog logged) (OracleComp spec')))
    (impl : QueryImpl spec' (StateT S ProbComp)) :
    QueryImpl spec (StateT (S × QueryLog logged) ProbComp) := fun t => StateT.mk fun state =>
  (fun result => (result.1.1, (result.2, state.2 ++ result.1.2))) <$> (simulateQ impl (so t).run).run state.1

theorem flattened_run (so : QueryImpl spec (WriterT (QueryLog logged) (OracleComp spec')))
    (impl : QueryImpl spec' (StateT S ProbComp)) (prog : OracleComp spec α) (s : S) (log : QueryLog logged) :
    (simulateQ (flattened so impl) prog).run (s, log) =
      (fun result => (result.1.1, (result.2, log ++ result.1.2))) <$> (simulateQ impl (simulateQ so prog).run).run s := by
  induction prog using OracleComp.inductionOn generalizing s log with
  | pure a => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, WriterT.run_bind', map_bind, flattened]
    change ((fun result => (result.1.1, (result.2, log ++ result.1.2))) <$> (simulateQ impl (so t).run).run s >>= _) = _
    rw [bind_map_left]
    apply bind_congr
    rintro ⟨⟨u, w⟩, s'⟩
    simp only [ih, simulateQ_map, StateT.run_map, Functor.map_map]
    congr 1
    funext result
    simp [List.append_assoc]

end Flatten

section Projection
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {S₁ S₂ α : Type}

/-- Adaptive execution respects a state projection when every single query does. -/
theorem evalDist_simulateQ_run_proj (h₁ : QueryImpl spec (StateT S₁ ProbComp)) (h₂ : QueryImpl spec (StateT S₂ ProbComp))
    (proj : S₂ → S₁)
    (hh : ∀ t s, ∀ [MeasurableSpace (spec.Range t × S₁)],
      𝒟[(h₁ t).run (proj s)] = 𝒟[Prod.map id proj <$> (h₂ t).run s])
    (prog : OracleComp spec α) (s : S₂) [MeasurableSpace (α × S₁)] :
    𝒟[(simulateQ h₁ prog).run (proj s)] = 𝒟[Prod.map id proj <$> (simulateQ h₂ prog).run s] := by
  induction prog using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    let : MeasurableSpace (spec.Range t × S₁) := ⊤
    let : MeasurableSpace (spec.Range t × S₂) := ⊤
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map, OracleQuery.input_query,
      StateT.run_bind, map_bind, evalDist_bind_of_discrete]
    rw [hh t s, evalDist_map_of_discrete, Measure.bind, Measure.bind,
      Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    congr 2
    funext output
    exact ih output.1 output.2

end Projection


section Concrete
variable (curve : Model.PairingCurve) (securityParameter : Nat) {Message : Type} [DecidableEq Message]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾₂" => curve.KeyGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Exponents and points, identified by the generator. -/
noncomputable def exponent : 𝔽 ≃ 𝔾₁ := Equiv.ofBijective _ (curve.generates securityParameter)

@[simp] theorem exponent_apply (r : 𝔽) : exponent curve securityParameter r = r • g₁ := rfl
@[simp] theorem exponent_symm_smul (point : 𝔾₁) : (exponent curve securityParameter).symm point • g₁ = point :=
  (exponent curve securityParameter).apply_symm_apply point
@[simp] theorem exponent_symm_apply (r : 𝔽) : (exponent curve securityParameter).symm (r • g₁) = r :=
  (exponent curve securityParameter).symm_apply_apply r
@[simp] theorem exponent_symm_smul_smul (secret : 𝔽) (point : 𝔾₁) :
    (exponent curve securityParameter).symm point • (secret • g₁) = secret • point := by
  rw [smul_comm, exponent_symm_smul]

abbrev Cache := (Message →ₒ 𝔾₁).QueryCache
abbrev Log := QueryLog (Message →ₒ 𝔾₁)

/-- The standard oracle's state, read as the exponent-keeping oracle's state. -/
noncomputable def project (state : Cache curve securityParameter (Message := Message) × Log curve securityParameter (Message := Message)) :
    ROM.State 𝔽 Message where
  hashExponents message := (state.1 message).map (exponent curve securityParameter).symm
  signedMessages := (state.2.map Sigma.fst).toFinset

theorem project_empty : project curve securityParameter (Message := Message) (∅, []) = ROM.State.empty := by
  simp [project, ROM.State.empty]

/-- The standard handler, flattened: pass-through plus BLS signing, run in the lazy random oracle. -/
noncomputable def standard (secret : 𝔽) :=
  flattened ((RandomOracle.Spec Message 𝔾₁).passthrough +
      (signature curve securityParameter (Message := Message)).signingOracle (secret • g₂) secret)
    (Message →ₒ 𝔾₁).romImpl

theorem standard_random (secret : 𝔽) (n : Nat) (state : Cache curve securityParameter (Message := Message) × Log curve securityParameter) :
    (standard curve securityParameter secret (ROM.Request.random n)).run state =
      (fun u => (u, state)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp [standard, flattened, ROM.Request.random, unifFwdImpl]


theorem standard_hash (secret : 𝔽) (message : Message) (state : Cache curve securityParameter (Message := Message) × Log curve securityParameter) :
    (standard curve securityParameter secret (ROM.Request.hash message)).run state =
      match state.1 message with
      | some point => pure (point, state)
      | none => ($ᵗ 𝔾₁ : ProbComp 𝔾₁) >>= fun point => pure (point, (state.1.cacheQuery message point, state.2)) := by
  simp [standard, flattened, ROM.Request.hash]
  cases state.1 message <;> simp

theorem standard_sign (secret : 𝔽) (message : Message) (state : Cache curve securityParameter (Message := Message) × Log curve securityParameter) :
    (standard curve securityParameter secret (ROM.Request.sign message)).run state =
      match state.1 message with
      | some point => pure (secret • point, (state.1, state.2 ++ [⟨message, secret • point⟩]))
      | none => ($ᵗ 𝔾₁ : ProbComp 𝔾₁) >>= fun point =>
          pure (secret • point, (state.1.cacheQuery message point, state.2 ++ [⟨message, secret • point⟩])) := by
  simp [standard, flattened, ROM.Request.sign, SignatureAlg.signingOracle, QueryImpl.withLogging_apply, signature,
    RandomOracle.hash]
  cases state.1 message <;> simp

theorem readable_hash (secret : 𝔽) (message : Message) (state : ROM.State 𝔽 Message) :
    (ROM.oracle (F := 𝔽) g₁ (secret • g₁) (ROM.Request.hash message)).run state =
      match state.hashExponents message with
      | some scalar => pure (scalar • g₁, state)
      | none => ($ᵗ 𝔽 : ProbComp 𝔽) >>= fun scalar =>
          pure (scalar • g₁, { state with hashExponents := Function.update state.hashExponents message (some scalar) }) := by
  simp [ROM.oracle, ROM.hashScalar, ROM.Request.hash]
  cases state.hashExponents message <;> simp

theorem readable_sign (secret : 𝔽) (message : Message) (state : ROM.State 𝔽 Message) :
    (ROM.oracle (F := 𝔽) g₁ (secret • g₁) (ROM.Request.sign message)).run state =
      match state.hashExponents message with
      | some scalar => pure (scalar • (secret • g₁), { state with signedMessages := insert message state.signedMessages })
      | none => ($ᵗ 𝔽 : ProbComp 𝔽) >>= fun scalar =>
          pure (scalar • (secret • g₁),
            { state with
              hashExponents := Function.update state.hashExponents message (some scalar)
              signedMessages := insert message state.signedMessages }) := by
  simp [ROM.oracle, ROM.hashScalar, ROM.Request.sign]
  cases state.hashExponents message <;> simp


theorem readable_random (secret : 𝔽) (n : Nat) (state : ROM.State 𝔽 Message) :
    (ROM.oracle (F := 𝔽) g₁ (secret • g₁) (ROM.Request.random n)).run state =
      (fun u => (u, state)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp [ROM.oracle, ROM.Request.random]

theorem project_cache (cache : Cache curve securityParameter (Message := Message)) (log : Log curve securityParameter)
    (message : Message) (point : 𝔾₁) :
    project curve securityParameter (cache.cacheQuery message point, log) =
      { project curve securityParameter (cache, log) with
        hashExponents := Function.update (project curve securityParameter (cache, log)).hashExponents message
          (some ((exponent curve securityParameter).symm point)) } := by
  simp only [project]
  congr 1
  funext other
  by_cases same : other = message
  · subst same; simp
  · simp [QueryCache.cacheQuery_of_ne cache point same, Function.update_of_ne same]

theorem project_log (cache : Cache curve securityParameter (Message := Message)) (log : Log curve securityParameter)
    (message : Message) (point : 𝔾₁) :
    project curve securityParameter (cache, log ++ [⟨message, point⟩]) =
      { project curve securityParameter (cache, log) with
        signedMessages := insert message (project curve securityParameter (cache, log)).signedMessages } := by
  simp only [project]
  congr 1
  ext x
  simp

theorem uniform_exponent {β : Type} [MeasurableSpace β] (f : 𝔾₁ → ProbComp β) :
    𝒟[($ᵗ 𝔽 : ProbComp 𝔽) >>= fun scalar => f (scalar • g₁)] = 𝒟[($ᵗ 𝔾₁ : ProbComp 𝔾₁) >>= f] := by
  let : MeasurableSpace 𝔽 := ⊤
  let : MeasurableSpace 𝔾₁ := ⊤
  exact evalDist_bind_bijective_uniform_cross _ _ evalDist_uniformSample evalDist_uniformSample _
    (curve.generates securityParameter) f

theorem query_project (secret : 𝔽) (request : (ROM.advSpec Message 𝔾₁).Domain)
    (state : Cache curve securityParameter (Message := Message) × Log curve securityParameter)
    [MeasurableSpace ((ROM.advSpec Message 𝔾₁).Range request × ROM.State 𝔽 Message)] :
    𝒟[(ROM.oracle (F := 𝔽) g₁ (secret • g₁) request).run (project curve securityParameter state)] =
      𝒟[Prod.map id (project curve securityParameter) <$> (standard curve securityParameter secret request).run state] := by
  rcases request with (n | message) | message
  · rw [readable_random, standard_random, Functor.map_map]
    rfl
  · rw [readable_hash, standard_hash]
    cases cached : state.1 message with
    | some point =>
      have cached' : (project curve securityParameter state).hashExponents message =
        some ((exponent curve securityParameter).symm point) := by simp [project, cached]
      simp [cached']
    | none =>
      have cached' : (project curve securityParameter state).hashExponents message = none := by simp [project, cached]
      simp only [cached', map_bind, map_pure, Prod.map_apply, id_eq, project_cache]
      rw [← uniform_exponent]
      simp
  · rw [readable_sign, standard_sign]
    cases cached : state.1 message with
    | some point =>
      have cached' : (project curve securityParameter state).hashExponents message =
        some ((exponent curve securityParameter).symm point) := by simp [project, cached]
      simp [cached', project_log]
    | none =>
      have cached' : (project curve securityParameter state).hashExponents message = none := by simp [project, cached]
      simp only [cached', map_bind, map_pure, Prod.map_apply, id_eq, project_cache, project_log]
      rw [← uniform_exponent]
      refine congrArg _ (bind_congr fun scalar => ?_)
      rw [smul_comm secret scalar]
      simp


theorem standard_run (secret : 𝔽) {α : Type} (prog : OracleComp (ROM.advSpec Message 𝔾₁) α) (cache : Cache curve securityParameter (Message := Message)) :
    (simulateQ (Message →ₒ 𝔾₁).romImpl (simulateQ ((RandomOracle.Spec Message 𝔾₁).passthrough +
        (signature curve securityParameter (Message := Message)).signingOracle (secret • g₂) secret) prog).run).run cache =
      (fun result => ((result.1, result.2.2), result.2.1)) <$> (simulateQ (standard curve securityParameter secret) prog).run (cache, []) := by
  rw [standard, flattened_run, Functor.map_map]
  simp

theorem not_wasQueried (log : Log curve securityParameter (Message := Message)) (message : Message) :
    (!log.wasQueried message) = decide (message ∉ (log.map Sigma.fst).toFinset) := by
  simp [QueryLog.wasQueried, QueryLog.getQ_ne_nil_iff_mem_map_fst]
  rw [← decide_not]
  simp only [not_forall, not_not]

theorem standard_hash_run (secret : 𝔽) (message : Message) (state : Cache curve securityParameter (Message := Message) × Log curve securityParameter) :
    (simulateQ (standard curve securityParameter secret) (ROM.hash message)).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (simulateQ (Message →ₒ 𝔾₁).romImpl (RandomOracle.hash message)).run state.1 := by
  simp [standard, flattened, ROM.hash, RandomOracle.hash]

/-- The attacker's run followed by the verifier's hash of the forged message. -/
def transcript (adversary : EufCma.Adversary (signature curve securityParameter (Message := Message))) (secret : 𝔽) :
    OracleComp (ROM.advSpec Message 𝔾₁) (Message × 𝔾₁ × 𝔾₁) := do
  let (message, point) ← adversary.main (secret • g₂)
  let hash ← ROM.hash message
  return (message, point, hash)

theorem standard_transcript (adversary : EufCma.Adversary (signature curve securityParameter (Message := Message))) (secret : 𝔽)
    (state : Cache curve securityParameter (Message := Message) × Log curve securityParameter) :
    (simulateQ (standard curve securityParameter secret) (transcript curve securityParameter adversary secret)).run state =
      (simulateQ (standard curve securityParameter secret) (adversary.main (secret • g₂))).run state >>= fun first =>
        (simulateQ (Message →ₒ 𝔾₁).romImpl (RandomOracle.hash first.1.1)).run first.2.1 >>= fun second =>
          pure ((first.1.1, first.1.2, second.1), (second.2, first.2.2)) := by
  simp only [transcript, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, standard_hash_run, bind_map_left]

theorem readable_transcript (adversary : EufCma.Adversary (signature curve securityParameter (Message := Message))) (secret : 𝔽)
    (state : ROM.State 𝔽 Message) :
    (simulateQ (ROM.oracle (F := 𝔽) g₁ (secret • g₁)) (transcript curve securityParameter adversary secret)).run state =
      (simulateQ (ROM.oracle (F := 𝔽) g₁ (secret • g₁)) (adversary.main (secret • g₂))).run state >>= fun first =>
        (simulateQ (ROM.oracle (F := 𝔽) g₁ (secret • g₁)) (ROM.hash first.1.1)).run first.2 >>= fun second =>
          pure ((first.1.1, first.1.2, second.1), second.2) := by
  simp [transcript, simulateQ_bind, StateT.run_bind]

/-- The standard experiment and the readable exponent-keeping game have the same distribution. -/
theorem eufCma_eq_rom (adversary : EufCma.Adversary (signature curve securityParameter (Message := Message))) :
    𝒟[eufCma curve securityParameter adversary] = 𝒟[rom curve securityParameter adversary.main] := by
  classical
  have keygen : (signature curve securityParameter (Message := Message)).keygen =
      liftM ($ᵗ 𝔽 : ProbComp 𝔽) >>= fun secret => pure (secret • g₂, secret) := rfl
  have verify : ∀ publicKey message point, (signature curve securityParameter (Message := Message)).verify publicKey message point =
      RandomOracle.hash message >>= fun hash => pure (decide (BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) point g₂ =
        BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash publicKey)) := fun _ _ _ => rfl
  have lhs : eufCma curve securityParameter adversary = ($ᵗ 𝔽 : ProbComp 𝔽) >>= fun secret =>
      (simulateQ (standard curve securityParameter secret) (transcript curve securityParameter adversary secret)).run (∅, []) >>=
        fun result => pure (!result.2.2.wasQueried result.1.1 && decide (BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) result.1.2.1 g₂ =
          BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) result.1.2.2 (secret • g₂))) := by
    simp only [eufCma, EufCma.game, SignatureAlg.unforgeableExperiment, SignatureAlg.runWithSigningOracle_def,
      RandomOracle.run, keygen, verify, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run'_eq,
      StateT.run_bind, StateT.run_pure, simulateQ_romImpl_liftM_run, map_bind, map_pure, bind_map_left, standard_run,
      standard_transcript]
    congr!
  have rhs : rom curve securityParameter adversary.main = ($ᵗ 𝔽 : ProbComp 𝔽) >>= fun secret =>
      (simulateQ (ROM.oracle (F := 𝔽) g₁ (secret • g₁)) (transcript curve securityParameter adversary secret)).run ROM.State.empty >>=
        fun result => pure (decide (BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) result.1.2.1 g₂ =
          BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) result.1.2.2 (secret • g₂)) && decide (result.1.1 ∉ result.2.signedMessages)) := by
    simp only [rom, readable_transcript, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [lhs, rhs]
  let : MeasurableSpace 𝔽 := ⊤
  let : MeasurableSpace ((Message × 𝔾₁ × 𝔾₁) × ROM.State 𝔽 Message) := ⊤
  let : MeasurableSpace ((Message × 𝔾₁ × 𝔾₁) × (Cache curve securityParameter (Message := Message) × Log curve securityParameter (Message := Message))) := ⊤
  simp only [evalDist_bind_of_discrete]
  congr 1
  funext secret
  rw [← project_empty curve securityParameter, evalDist_simulateQ_run_proj _ _ _
    (fun request state => query_project curve securityParameter secret request state) _ (∅, []),
    evalDist_map_of_discrete, Measure.bind, Measure.bind, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  congr 2
  funext result
  simp only [QueryLog.wasQueried, QueryLog.getQ_ne_nil_iff_mem_map_fst, List.mem_map, decide_not]
  simp [project, Bool.and_comm]

end Concrete
end BLS.Game
