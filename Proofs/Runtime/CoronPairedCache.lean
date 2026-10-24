import Proofs.Runtime.CoronErasure
import Proofs.Runtime.LazyAGMExecution

/-! A paired, lazy cache for the Coron reduction. Each stored entry contains
the scalar and coin sampled for one message. Projection recovers both original
caches and the signing set, including for shadowed initial entries. The source
equalities preserve oracle computations, not just their output distributions.
The representation functions here are proof views, not executed operations. -/
namespace Signatures.Runtime.Coron.Paired
open OracleComp OracleSpec

abbrev State (F M G : Type) (qS : Nat) := LazyAGM.State M (F × Fin (qS + 1)) G

variable {F M G : Type} {qS : Nat} [DecidableEq M]

def scalars (entries : List (M × (F × Fin (qS + 1)))) (message : M) : Option F :=
  Prod.fst <$> entries.lookup message

def coins (entries : List (M × (F × Fin (qS + 1)))) : (M →ₒ Fin (qS + 1)).QueryCache :=
  .ofFn (fun message => Prod.snd <$> entries.lookup message)

theorem coins_apply (entries : List (M × (F × Fin (qS + 1)))) (message : M) :
    coins entries message = Prod.snd <$> entries.lookup message := rfl

def nativeState (state : State F M G qS) : NativeState F M qS :=
  ((scalars state.1, (state.2.2.map Prod.fst).toFinset), coins state.1)

theorem scalars_cons (entries : List (M × (F × Fin (qS + 1)))) (message : M)
    (entry : F × Fin (qS + 1)) :
    scalars ((message, entry) :: entries) = Function.update (scalars entries) message (some entry.1) := by
  funext query
  by_cases equal : query = message
  · subst query; simp [scalars]
  · simp [scalars, List.lookup_cons, beq_eq_false_iff_ne.mpr equal, equal]

theorem coins_cons (entries : List (M × (F × Fin (qS + 1)))) (message : M)
    (entry : F × Fin (qS + 1)) :
    coins ((message, entry) :: entries) = (coins entries).cacheQuery message entry.2 := by
  apply QueryCache.ext
  intro query
  by_cases equal : query = message
  · subst query; simp [coins]
  · simp [coins, List.lookup_cons, beq_eq_false_iff_ne.mpr equal, equal, QueryCache.cacheQuery_of_ne]

theorem nativeState_empty : nativeState (([], ([], [])) : State F M G qS) = ((fun _ => none, ∅), ∅) := rfl

variable [Field F] [SampleableType F] [AddCommGroup G] [Module F G]

def response (g X h : G) (signing : Bool) (entry : F × Fin (qS + 1)) : G :=
  if signing then (if entry.2 = 0 then 0 else entry.1 • X)
  else entry.1 • g + if entry.2 = 0 then h else 0

omit [Field F] in
private theorem sample_pair : ($ᵗ (F × Fin (qS + 1)) : ProbComp _) = (do
    let scalar ← ($ᵗ F : ProbComp F)
    (fun coin => (scalar, coin)) <$> ($ᵗ (Fin (qS + 1)) : ProbComp _)) := by
  change ((Prod.mk <$> ($ᵗ F : ProbComp F)) <*> ($ᵗ (Fin (qS + 1)) : ProbComp _)) = _
  simp only [seq_eq_bind_map, bind_map_left]

/-- A paired cache hit samples neither component. A miss samples the scalar
then the coin, exactly as in the original two-cache oracle. -/
theorem reply_native (g X h : G) (signing : Bool) (message : M) (state : State F M G qS) :
    Prod.map id nativeState <$>
      (LazyAGM.listReply signing (response g X h signing) message).run state =
        (nativeReply g X h qS signing message).run (nativeState state) := by
  rcases state with ⟨entries, hashed, signed⟩
  have lookup := BLS.LazyAGM.Reduction.privateListOracle_lookup (R := F × Fin (qS + 1)) message entries
  simp only [StateT.run] at lookup
  simp only [LazyAGM.listReply, StateT.run]
  rw [lookup]
  cases found : entries.lookup message with
  | some entry =>
    cases signing <;>
      simp [found, nativeReply, nativeState, scalars, coins_apply, BLS.ROM.Internal.getDlogS,
        LazyAGM.record, response]
  | none =>
    cases signing <;>
      simp [found, nativeReply, nativeState, scalars, coins_apply, BLS.ROM.Internal.getDlogS,
        LazyAGM.record, response, sample_pair, scalars_cons, coins_cons,
        map_bind, bind_map_left]

noncomputable def oracle (g X h : G) :
    QueryImpl (BLS.ROM.advSpec M G) (StateT (State F M G qS) ProbComp) :=
  LazyAGM.listOracle (response g X h false) (response g X h true)

theorem oracle_native (g X h : G) (query : (BLS.ROM.advSpec M G).Domain) (state : State F M G qS) :
    Prod.map id nativeState <$> (oracle g X h query).run state =
      (nativeOracle g X h qS query).run (nativeState state) := by
  rcases query with ((range | message) | message)
  · simp [oracle, LazyAGM.listOracle, nativeOracle, StateT.run, Functor.map_map]
  · exact reply_native g X h false message state
  · exact reply_native g X h true message state

/-- The joint cache and signing-set correspondence holds for every adaptive
oracle computation, without an arithmetic-language condition on its caller. -/
theorem simulation_native {A : Type} (g X h : G) (program : OracleComp (BLS.ROM.advSpec M G) A)
    (state : State F M G qS) :
    Prod.map id nativeState <$> (simulateQ (oracle g X h) program).run state =
      (simulateQ (nativeOracle g X h qS) program).run (nativeState state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ nativeState (oracle_native g X h) program state

/-- The final verification hash uses the same cache, even if the forgery's
message has not appeared before. Extraction reads its scalar component. -/
noncomputable def reduction (g X h : G) (program : BLS.ROM.Adversary M G) : ProbComp G :=
  (fun result => result.1.2 - (scalars result.2.1 result.1.1).getD 0 • X) <$>
    (simulateQ (oracle (F := F) (qS := qS) g X h) (BLS.ROM.cacheForgery program)).run ([], ([], []))

theorem reduction_native (g X h : G) (program : BLS.ROM.Adversary M G) :
    reduction (F := F) (qS := qS) g X h program = nativeReduction (F := F) g X h qS program := by
  rw [nativeReduction_cached]
  have simulated := simulation_native (F := F) (qS := qS) g X h (BLS.ROM.cacheForgery program) ([], ([], []))
  rw [nativeState_empty] at simulated
  rw [← simulated]
  simp only [reduction, Functor.map_map]
  rfl

theorem reduction_original {K : Type} (g X h : G) (keyGenerator publicKey : K)
    (adversary : BLS.ROM.AdversaryPK M G K) :
    reduction (F := F) (qS := qS) g X h (adversary publicKey) =
      BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.ROM.cacheForgeryPK adversary)
        g keyGenerator X publicKey h :=
  (reduction_native g X h (adversary publicKey)).trans
    (nativeReduction_original g X h keyGenerator publicKey qS adversary)

/-- Only encountered messages occupy cache entries. The stored reply logs also
grow by at most the caller's query count, for arbitrary adaptive queries. -/
theorem simulation_growth {A : Type} (g X h : G) (program : OracleComp (BLS.ROM.advSpec M G) A)
    (state : State F M G qS) (queries : Nat) (bounded : IsTotalQueryBound program queries)
    (result : A × State F M G qS)
    (reached : result ∈ support ((simulateQ (oracle g X h) program).run state)) :
    result.2.1.length ≤ state.1.length + queries ∧
      result.2.2.1.length + result.2.2.2.length ≤ state.2.1.length + state.2.2.length + queries :=
  LazyAGM.listSimulation_growth (response g X h false) (response g X h true) program state queries bounded result reached

end Signatures.Runtime.Coron.Paired
