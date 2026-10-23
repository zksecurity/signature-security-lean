import Signatures.Model.DirectAGM
import Signatures.Model.Proofs.AlgebraicOracle

open OracleComp OracleSpec

namespace Model.DirectAGM

open AlgebraicGroupModel.Interaction
open LazyAGM.Interactive

private theorem simulate_queryBind {I α : Type} {spec : OracleSpec I}
    {N : Type → Type} [Monad N] [LawfulMonad N]
    (impl : QueryImpl spec N) (request : I) (next : spec.Range request → OracleComp spec α) :
    simulateQ impl (OracleComp.queryBind request next) =
      impl request >>= fun reply => simulateQ impl (next reply) := by
  change simulateQ impl ((liftM (spec.query request) : OracleComp spec _) >>= next) = _
  rw [simulateQ_bind, simulateQ_spec_query]

variable {F Index Message G₁ G₂ : Type}
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

namespace ProofView

theorem weighted_append {D : Type} (coeff : List F) (replies : List (D × G₁))
    (sameLength : coeff.length = replies.length) (c : F) (reply : D × G₁) :
    LazyAGM.weightedReplies (coeff ++ [c]) (replies ++ [reply]) =
      LazyAGM.weightedReplies coeff replies + c • reply.2 := by
  unfold LazyAGM.weightedReplies
  rw [List.mapIdx_append_one, List.sum_append]
  congr 1
  · congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_mapIdx]
      have bound : i < coeff.length := by simpa [sameLength] using hi
      simp only [LazyAGM.tokenCoeff, List.getElem?_append_left bound]
  · simp [LazyAGM.tokenCoeff, sameLength]

/-- A chronological basis and its grouped proof view evaluate every vector identically. -/
structure Aligned (generator : G₁) (positions : Positions)
    (basis : Groups (Group G₁ G₂)) (transcript : LazyAGM.Transcript Index Message G₁) : Prop where
  next_eq : positions.next = (basis .signature).length
  hashes_length : positions.hashes.length = transcript.1.length
  signatures_length : positions.signatures.length = transcript.2.length
  evaluate_eq : ∀ coeff : List F,
    evaluate coeff (basis .signature) =
      LazyAGM.tokenCoeff coeff 0 • generator +
      LazyAGM.weightedReplies (positions.hashes.map (LazyAGM.tokenCoeff coeff)) transcript.1 +
      LazyAGM.weightedReplies (positions.signatures.map (LazyAGM.tokenCoeff coeff)) transcript.2

omit [AddCommGroup G₂] [Module F G₂] in
theorem aligned_initial (generator : G₁) (publicKey : G₂) :
    Aligned (F := F) (Index := Index) (Message := Message) generator {}
      (initialInput generator publicKey).groups ([], []) := by
  constructor <;> simp [initialInput, groupLists, evaluate, LazyAGM.weightedReplies,
    LazyAGM.tokenCoeff]

omit [AddCommGroup G₂] [Module F G₂] in
theorem Aligned.request {generator : G₁} {positions : Positions}
    {basis : Groups (Group G₁ G₂)} {transcript : LazyAGM.Transcript Index Message G₁}
    (aligned : Aligned (F := F) generator positions basis transcript)
    (request : AlgebraicGroupModel.Interaction.Message (Query Index Message) (Group G₁ G₂)) :
    Aligned (F := F) generator (positions.request request) basis transcript :=
  ⟨aligned.next_eq, aligned.hashes_length, aligned.signatures_length, aligned.evaluate_eq⟩

omit [AddCommGroup G₂] [Module F G₂] in
theorem Aligned.hash {generator : G₁} {positions : Positions}
    {basis : Groups (Group G₁ G₂)} {transcript : LazyAGM.Transcript Index Message G₁}
    (aligned : Aligned (F := F) generator positions basis transcript) (index : Index) (point : G₁) :
    Aligned (F := F) generator positions.hash (extend basis (groupLists [point] []))
      (transcript.1 ++ [(index, point)], transcript.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Positions.hash, extend, groupLists] using aligned.next_eq
  · simpa [Positions.hash] using aligned.hashes_length
  · exact aligned.signatures_length
  · intro coeff
    simp only [extend, groupLists, evaluate, List.mapIdx_append_one, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    rw [← evaluate, aligned.evaluate_eq]
    simp only [Positions.hash, List.map_append, List.map_cons, List.map_nil]
    rw [weighted_append _ _ (by simpa using aligned.hashes_length)]
    rw [aligned.next_eq]
    simp only [LazyAGM.tokenCoeff]
    abel

omit [AddCommGroup G₂] [Module F G₂] in
theorem Aligned.sign {generator : G₁} {positions : Positions}
    {basis : Groups (Group G₁ G₂)} {transcript : LazyAGM.Transcript Index Message G₁}
    (aligned : Aligned (F := F) generator positions basis transcript) (message : Message) (point : G₁) :
    Aligned (F := F) generator positions.sign (extend basis (groupLists [point] []))
      (transcript.1, transcript.2 ++ [(message, point)]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Positions.sign, extend, groupLists] using aligned.next_eq
  · exact aligned.hashes_length
  · simpa [Positions.sign] using aligned.signatures_length
  · intro coeff
    simp only [extend, groupLists, evaluate, List.mapIdx_append_one, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    rw [← evaluate, aligned.evaluate_eq]
    simp only [Positions.sign, List.map_append, List.map_cons, List.map_nil]
    rw [weighted_append _ _ (by simpa using aligned.signatures_length)]
    rw [aligned.next_eq]
    simp only [LazyAGM.tokenCoeff, add_assoc]

theorem head_evaluate (output : Explained F Message (Group G₁ G₂))
    (basis : Groups (Group G₁ G₂)) (valid : output.Valid basis) :
    evaluate (coefficients output) (basis .signature) =
      (output.value.groups .signature).headD 0 := by
  have h := valid .signature
  change evaluate ((output.coefficients .signature).headD []) (basis .signature) = _
  generalize output.value.groups .signature = points at h ⊢
  generalize output.coefficients .signature = vectors at h ⊢
  cases h with
  | nil => simp [evaluate, List.mapIdx_eq_ofFn]
  | cons first rest => exact first.2

theorem grouped_value (output : Explained F Message (Group G₁ G₂))
    {generator : G₁} {positions : Positions} {basis : Groups (Group G₁ G₂)}
    {transcript : LazyAGM.Transcript Index Message G₁}
    (aligned : Aligned (F := F) generator positions basis transcript)
    (valid : output.Valid basis) :
    LazyAGM.materialize generator (grouped output positions) transcript =
      (output.value.groups .signature).headD 0 := by
  rw [LazyAGM.materialize_eq_weightedReplies]
  exact (aligned.evaluate_eq (coefficients output)).symm.trans (head_evaluate output basis valid)

def observe (generator : G₁) (value : LazyAGM.Output F Message ×
    LazyAGM.Transcript Index Message G₁) : AlgebraicOracle.Result F Message G₁ where
  message := value.1.mstar
  signature := LazyAGM.materialize generator value.1 value.2
  signedMessages := value.2.2.map Prod.fst
  signingCoefficients := value.1.ξ

def execute {N : Type → Type} [Monad N]
    (random : QueryImpl unifSpec N) (hash : Index → N G₁) (sign : Message → N G₁)
    (attack : OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
      (Explained F Message (Group G₁ G₂)))
    (basis : Groups (Group G₁ G₂)) (state : State Message) :
    N ((Explained F Message (Group G₁ G₂) × Groups (Group G₁ G₂)) × State Message) :=
  ((simulateQ (fun request : Explained F (Query Index Message) (Group G₁ G₂) =>
    StateT.mk fun received => do
    let reply ← oracle random hash sign request.value
    pure (reply, extend received reply.groups)) attack).run basis).run state

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem execute_pure {N : Type → Type} [Monad N] [LawfulMonad N]
    (random : QueryImpl unifSpec N) (hash : Index → N G₁) (sign : Message → N G₁)
    (output : Explained F Message (Group G₁ G₂))
    (basis : Groups (Group G₁ G₂)) (state : State Message) :
    execute random hash sign (pure output) basis state = pure ((output, basis), state) := rfl

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem execute_query {N : Type → Type} [Monad N] [LawfulMonad N]
    (random : QueryImpl unifSpec N) (hash : Index → N G₁) (sign : Message → N G₁)
    (request : Explained F (Query Index Message) (Group G₁ G₂))
    (next : AlgebraicGroupModel.Interaction.Message (Reply request.value.data) (Group G₁ G₂) →
      OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
        (Explained F Message (Group G₁ G₂)))
    (basis : Groups (Group G₁ G₂)) (state : State Message) :
    execute random hash sign (OracleComp.queryBind request next) basis state =
      (oracle random hash sign request.value).run state >>= fun (reply, state) =>
      execute random hash sign (next reply) (extend basis reply.groups) state := by
  simp [execute, simulateQ, PFunctor.FreeM.liftM, StateT.run_bind, StateT.run_mk]

omit [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem program_random (n : Nat) (groups : Groups (Group G₁ G₂))
    (explanations : GroupSort → List (List F))
    (next : AlgebraicGroupModel.Interaction.Message (Fin (n + 1)) (Group G₁ G₂) →
      OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
        (Explained F Message (Group G₁ G₂))) (positions : Positions) :
    program (OracleComp.queryBind ⟨⟨.inl (.inl n), groups⟩, explanations⟩ next) positions =
      OracleComp.queryBind (.inl (.inl n)) (fun number =>
        program (next ⟨number, fun _ => []⟩)
          (positions.request (Index := Index) (Message := Message) ⟨.inl (.inl n), groups⟩)) := rfl

omit [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem program_hash (index : Index) (groups : Groups (Group G₁ G₂))
    (explanations : GroupSort → List (List F))
    (next : AlgebraicGroupModel.Interaction.Message Unit (Group G₁ G₂) →
      OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
        (Explained F Message (Group G₁ G₂))) (positions : Positions) :
    program (OracleComp.queryBind ⟨⟨.inl (.inr index), groups⟩, explanations⟩ next) positions =
      OracleComp.queryBind (.inl (.inr index)) (fun point =>
        program (next ⟨(), groupLists [point] []⟩)
          (positions.request (Message := Message) ⟨.inl (.inr index), groups⟩).hash) := rfl

omit [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem program_sign (message : Message) (groups : Groups (Group G₁ G₂))
    (explanations : GroupSort → List (List F))
    (next : AlgebraicGroupModel.Interaction.Message Unit (Group G₁ G₂) →
      OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
        (Explained F Message (Group G₁ G₂))) (positions : Positions) :
    program (OracleComp.queryBind ⟨⟨.inr message, groups⟩, explanations⟩ next) positions =
      OracleComp.queryBind (.inr message) (fun point =>
        program (next ⟨(), groupLists [point] []⟩)
          (positions.request (Index := Index) ⟨.inr message, groups⟩).sign) := rfl

theorem execute_eq {N : Type → Type} [Monad N] [LawfulMonad N]
    (random : QueryImpl unifSpec N) (hash : Index → N G₁) (sign : Message → N G₁)
    (attack : OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
      (Explained F Message (Group G₁ G₂)))
    (generator : G₁) (basis : Groups (Group G₁ G₂)) (state : State Message)
    (transcript : LazyAGM.Transcript Index Message G₁)
    (algebraic : IsAlgebraic basis attack)
    (aligned : Aligned (F := F) generator state.positions basis transcript)
    (signed : state.signedMessages = transcript.2.map Prod.fst) :
    (fun value => (result value.1.1 value.2).toResult) <$>
      execute random hash sign attack basis state =
    observe generator <$>
      (simulateQ (LazyAGM.handler random hash sign) (program attack state.positions)).run transcript := by
  induction attack using OracleComp.recOn generalizing basis state transcript with
  | pure output =>
      change (fun value => (result value.1.1 value.2).toResult) <$>
        pure ((output, basis), state) = observe generator <$> pure (grouped output state.positions, transcript)
      simp only [map_pure]
      congr 1
      simp only [result, observe]
      rw [grouped_value output aligned algebraic, signed]
      rfl
  | queryBind request next ih =>
      obtain ⟨_, algebraicNext⟩ := (isAlgebraic_query basis request next).mp algebraic
      rcases request with ⟨⟨request, groups⟩, explanations⟩
      rcases request with ((n | index) | message)
      all_goals
        rw [execute_query]
        first
        | rw [program_random n groups explanations next state.positions]
        | rw [program_hash index groups explanations next state.positions]
        | rw [program_sign message groups explanations next state.positions]
        simp only [simulate_queryBind, StateT.run_bind, StateT.run_mk,
          oracle, LazyAGM.handler, StateT.run_modify, StateT.run_monadLift,
          bind_assoc, pure_bind, map_bind, StateT.run_pure, monadLift_self]
      · apply bind_congr
        intro number
        apply ih
        · exact algebraicNext ⟨number, fun _ => []⟩
        · have empty : extend basis (fun _ => []) = basis := by funext s; simp [extend]
          rw [empty]
          exact aligned.request ⟨.inl (.inl n), groups⟩
        · exact signed
      · apply bind_congr
        intro point
        apply ih
        · exact algebraicNext ⟨(), groupLists [point] []⟩
        · exact (aligned.request ⟨.inl (.inr index), groups⟩).hash index point
        · exact signed
      · apply bind_congr
        intro signature
        apply ih
        · exact algebraicNext ⟨(), groupLists [signature] []⟩
        · exact (aligned.request ⟨.inr message, groups⟩).sign message signature
        · simpa using congrArg (· ++ [message]) signed

omit [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem program_query_bound
    (attack : OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
      (Explained F Message (Group G₁ G₂)))
    (positions : Positions) (predicate : Query Index Message → Prop) [DecidablePred predicate] (limit : Nat)
    (bound : IsQueryBoundP attack (fun request => predicate request.value.data) limit) :
    IsQueryBoundP (program attack positions) predicate limit := by
  classical
  induction attack using OracleComp.recOn generalizing positions limit with
  | pure output => exact isQueryBoundP_pure _ _ _
  | queryBind request next ih =>
      change (¬ predicate request.value.data ∨ 0 < limit) ∧
        (∀ reply, IsQueryBoundP (next reply) (fun q => predicate q.value.data)
          (if predicate request.value.data then limit - 1 else limit)) at bound
      rcases request with ⟨⟨request, groups⟩, explanations⟩
      rcases request with ((n | index) | message)
      · rw [program_random n groups explanations next positions]
        exact ⟨bound.1, fun number => ih ⟨number, fun _ => []⟩ _ _ (bound.2 _)⟩
      · rw [program_hash index groups explanations next positions]
        exact ⟨bound.1, fun point => ih ⟨(), groupLists [point] []⟩ _ _ (bound.2 _)⟩
      · rw [program_sign message groups explanations next positions]
        exact ⟨bound.1, fun point => ih ⟨(), groupLists [point] []⟩ _ _ (bound.2 _)⟩

theorem adversary_query_bound (generator : G₁) (attack : Adversary F Index Message G₁ G₂)
    (publicKey : G₂) (predicate : Query Index Message → Prop) [DecidablePred predicate] (limit : Nat)
    (bound : IsQueryBoundP (attack.main (initialInput generator publicKey))
      (fun request => predicate request.value.data) limit) :
    IsQueryBoundP ((adversary generator attack).main publicKey) predicate limit :=
  program_query_bound _ _ _ _ bound

end ProofView

/-- Every shared-library attacker has this exact grouped proof view, without extra assumptions. -/
theorem run_eq (terms : Message → List (Index × F)) (secret : F)
    (attack : Adversary F Index Message G₁ G₂) (generator : G₁) (publicKey : G₂) :
    Result.toResult <$> run terms secret attack generator publicKey =
      AlgebraicOracle.run terms secret (ProofView.adversary generator attack) generator publicKey := by
  rw [AlgebraicOracle.run_eq]
  have same := ProofView.execute_eq RandomOracle.random RandomOracle.hash
    (AlgebraicOracle.sign terms secret) (attack.main (initialInput generator publicKey))
    generator (initialInput generator publicKey).groups {} ([], [])
    (attack.algebraic _) (ProofView.aligned_initial generator publicKey) rfl
  simp only [run, runWith, bind_pure_comp, Functor.map_map]
  convert same using 1 <;> rfl

theorem run_bind_eq {α : Type} (terms : Message → List (Index × F)) (secret : F)
    (attack : Adversary F Index Message G₁ G₂) (generator : G₁) (publicKey : G₂)
    (next : AlgebraicOracle.Result F Message G₁ → RandomOracle.Computation Index G₁ α) :
    (run terms secret attack generator publicKey >>= fun result => next result.toResult) =
      (AlgebraicOracle.run terms secret (ProofView.adversary generator attack) generator publicKey >>= next) := by
  rw [← run_eq]
  simp only [bind_map_left]

section Security

variable {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
  [SampleableType F] [SampleableType G₁] [DecidableEq Index]

/-- Dropping only protocol-shape rejection gives exactly the existing proof-side game. -/
theorem unchecked_game_eq
    (terms : Message → List (Index × F)) (admissible : Message → List Message → Prop)
    (generator : G₁) (keyGenerator : G₂) (attack : Adversary F Index Message G₁ G₂) :
    (by
      classical
      exact RandomOracle.run do
        let secret ← RandomOracle.sample F
        let forgery ← run terms secret attack generator (secret • keyGenerator)
        let hash ← AlgebraicOracle.hashMessage terms forgery.message
        return decide (admissible forgery.message forgery.signedMessages ∧
          BilinearGroup.pairing (F := F) (Gₜ := Gₜ) forgery.signature keyGenerator =
            BilinearGroup.pairing (F := F) (Gₜ := Gₜ) hash (secret • keyGenerator) ∧
          forgery.message ∉ forgery.signedMessages)) =
      LazyAGM.game (Gₜ := Gₜ) terms admissible generator keyGenerator
        (ProofView.adversary generator attack) := by
  classical
  rw [← AlgebraicOracle.game_eq]
  apply congrArg RandomOracle.run
  apply bind_congr
  intro secret
  rw [← run_eq]
  simp only [bind_map_left]

/-- The native game is bounded by the reduction's internally derived coefficient game.
Malformed outputs are rejected by the native game and cannot increase its success. -/
theorem game_le
    (terms : Message → List (Index × F)) (admissible : Message → List Message → Prop)
    (generator : G₁) (keyGenerator : G₂) (attack : Adversary F Index Message G₁ G₂) :
    𝒟[game (Gₜ := Gₜ) terms admissible generator keyGenerator attack] {true} ≤
      𝒟[LazyAGM.game (Gₜ := Gₜ) terms admissible generator keyGenerator
        (ProofView.adversary generator attack)] {true} := by
  classical
  rw [← unchecked_game_eq]
  simp only [game, RandomOracle.run, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨secret, cache⟩ _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨forgery, cache⟩ _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨hash, cache⟩ _
  by_cases wellFormed : forgery.wellFormed <;> simp [wellFormed]

end Security

end Model.DirectAGM
