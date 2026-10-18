import Signatures.Runtime.Caliper.BLSReplySchemes
import Signatures.Runtime.Caliper.BLSCacheReachability
import Signatures.Runtime.Caliper.BLSRecordReachability

/-! A single reachable-state invariant for the complete BLS reply. Cache entries,
reply logs and configuration remain represented, with capacity reserved for all
remaining calls. Output-domain preservation follows from the constructed handler
and the primitive sampling law, rather than a separate response-function premise. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM

variable {w : Nat} {M R C G : Type} [DecidableEq M] (layout : Layouts w M R C G)

structure Reserved (remaining : Nat) (saved : Store M R C G) : Prop where
  config : layout.config.valid saved.1
  cached : BLSCache.entriesFit layout.cache saved.2.1
  recorded : BLSRecord.entriesFit layout.records saved.2.2
  cacheRoom : saved.2.1.length + remaining ≤ layout.cache.capacityPred + 1
  logRoom : saved.2.2.1.length + saved.2.2.2.length + remaining ≤ layout.capacityPred + 1

namespace Reserved
variable {layout} {saved : Store M R C G} {small large : Nat}

omit [DecidableEq M] in
theorem weaken (reserved : Reserved layout large saved) (bound : small ≤ large) : Reserved layout small saved :=
  ⟨reserved.config, reserved.cached, reserved.recorded, by have := reserved.cacheRoom; omega,
    by have := reserved.logRoom; omega⟩

theorem ready {remaining : Nat} (reserved : Reserved layout (remaining + 1) saved)
    (default : layout.cache.value.Value) (signing : Bool) (message : M) (messageFits : layout.cache.key.valid message) :
    (layout.input default.val signing).valid (message, saved) := by
  have cacheRoom := reserved.cacheRoom
  have logRoom := reserved.logRoom
  change (layout.cache.key.valid message ∧ layout.config.valid saved.1 ∧
    (saved.2.1.length ≤ layout.cache.capacityPred + 1 ∧ BLSCache.entriesFit layout.cache saved.2.1) ∧
    (saved.2.2.1.length ≤ layout.capacityPred + 1 ∧ _) ∧ (saved.2.2.2.length ≤ layout.capacityPred + 1 ∧ _)) ∧
    layout.cache.admissible (message, default.val, saved.2.1, ()) ∧ _
  refine ⟨⟨messageFits, reserved.config, ⟨by omega, reserved.cached⟩,
    ⟨by omega, reserved.recorded.1⟩, ⟨by omega, reserved.recorded.2⟩⟩, (fun _ => by change saved.2.1.length ≤ layout.cache.capacityPred; omega), ?_⟩
  cases signing <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

omit [DecidableEq M] in
theorem of_output {remaining : Nat} {answer : G} {saved : Store M R C G}
    (valid : layout.output.valid (answer, saved))
    (cacheRoom : saved.2.1.length + remaining ≤ layout.cache.capacityPred + 1)
    (logRoom : saved.2.2.1.length + saved.2.2.2.length + remaining ≤ layout.capacityPred + 1) :
    Reserved layout remaining saved :=
  ⟨valid.2.1, valid.2.2.1.2, ⟨valid.2.2.2.1.2, valid.2.2.2.2.2⟩, cacheRoom, logRoom⟩

end Reserved

variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)
    (drawSource : ProbComp layout.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include default P comparison correct response responseBuffers reserve drawLaw in
theorem reply_output (signing : Bool) (value : (layout.input default.val signing).Value)
    (answer : G × LazyAGM.State (key.Value base) (val.Value base) G)
    (supported : answer ∈ support ((LazyAGM.listReply signing (fun sample => respond signing (sample, value.val.2.1)) value.val.1).run value.val.2.2)) :
    layout.output.valid (answer.1, value.val.2.1, answer.2) := by
  have law := denote_source layout default signing P comparison correct (response signing) (responseBuffers signing) reserve drawSource drawLaw value
  have mapped : (answer.1, value.val.2.1, answer.2) ∈ support
      (Subtype.val <$> denote layout default signing P comparison correct (response signing) (responseBuffers signing) reserve drawSource value) := by
    rw [law]
    simp only [support_map, Set.mem_image]
    exact ⟨answer, supported, rfl⟩
  simp only [support_map, Set.mem_image] at mapped
  obtain ⟨represented, _, equal⟩ := mapped
  exact equal ▸ represented.property

include default P comparison correct response responseBuffers reserve drawLaw in
theorem reply_reserved {remaining : Nat} {cfg : C} {state : LazyAGM.State (key.Value base) (val.Value base) G}
    (reserved : Reserved layout (remaining + 1) (cfg, state))
    (signing : Bool) (message : key.Value base) (messageFits : layout.cache.key.valid message)
    (answer : G × LazyAGM.State (key.Value base) (val.Value base) G)
    (supported : answer ∈ support ((LazyAGM.listReply signing (fun sample => respond signing (sample, cfg)) message).run state)) :
    Reserved layout remaining (cfg, answer.2) := by
  have valid := reply_output layout default P comparison correct response responseBuffers reserve drawSource drawLaw signing
    ⟨(message, cfg, state), reserved.ready default signing message messageFits⟩ answer supported
  have growth := LazyAGM.listReply_growth signing (fun sample => respond signing (sample, cfg)) message state answer supported
  have cacheRoom := reserved.cacheRoom
  have logRoom := reserved.logRoom
  apply Reserved.of_output valid
  all_goals dsimp only [Prod.fst, Prod.snd] at cacheRoom logRoom ⊢; omega

include default P comparison correct response responseBuffers reserve drawLaw in
theorem query_reserved {remaining : Nat} {cfg : C} {state : LazyAGM.State (key.Value base) (val.Value base) G}
    (reserved : Reserved layout (remaining + 1) (cfg, state))
    (query : (advSpec (key.Value base) (key.Value base) G).Domain)
    (allowed : BLSRecord.allowedQuery layout.records query)
    (answer : (advSpec (key.Value base) (key.Value base) G).Range query × LazyAGM.State (key.Value base) (val.Value base) G)
    (supported : answer ∈ support ((LazyAGM.listOracle (fun sample => respond false (sample, cfg))
      (fun sample => respond true (sample, cfg)) query).run state)) : Reserved layout remaining (cfg, answer.2) := by
  rcases query with ((n | message) | message)
  · rw [LazyAGM.listOracle_random] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    exact reserved.weaken (Nat.le_succ _)
  · exact reply_reserved layout default P comparison correct response responseBuffers reserve drawSource drawLaw reserved false message allowed answer supported
  · exact reply_reserved layout default P comparison correct response responseBuffers reserve drawSource drawLaw reserved true message allowed answer supported

include default P comparison correct response responseBuffers reserve drawLaw in
/-- Every supported adaptive prefix reserves room for all remaining calls.
Randomness, hashing and signing are all steps of the original source oracle. -/
theorem prefix_reserved {A : Type} {main residual : OracleComp (advSpec (key.Value base) (key.Value base) G) A}
    {cfg : C} {initial state : LazyAGM.State (key.Value base) (val.Value base) G} {used budget : Nat}
    (initialReady : Reserved layout budget (cfg, initial))
    (queries : AllQueriesSatisfy main (BLSRecord.allowedQuery layout.records))
    (bounded : IsTotalQueryBound main budget)
    (path : SourcePrefix (LazyAGM.listOracle (fun sample => respond false (sample, cfg)) (fun sample => respond true (sample, cfg)))
      main initial residual state used) : Reserved layout (budget - used) (cfg, state) := by
  induction path with
  | start => exact initialReady
  | @step query next state used path answer supported ih =>
    have positive := (path.queryBound bounded).2.1
    have before : Reserved layout ((budget - (used + 1)) + 1) (cfg, state) := by
      convert ih using 1; omega
    exact query_reserved layout default P comparison correct response responseBuffers reserve drawSource drawLaw before query
      (path.allowed queries).1 answer supported

include default P comparison correct response responseBuffers reserve drawLaw in
/-- The actual full reply input guard is derived at each source query. Neither
cache room nor transcript room is supplied as a per-query attacker contract. -/
theorem prefix_ready {A : Type} {main : OracleComp (advSpec (key.Value base) (key.Value base) G) A}
    {cfg : C} {initial state : LazyAGM.State (key.Value base) (val.Value base) G} {used budget : Nat}
    (initialReady : Reserved layout budget (cfg, initial))
    (queries : AllQueriesSatisfy main (BLSRecord.allowedQuery layout.records))
    (bounded : IsTotalQueryBound main budget) (signing : Bool) (message : key.Value base)
    (next : (advSpec (key.Value base) (key.Value base) G).Range (BLSRecord.request signing message) →
      OracleComp (advSpec (key.Value base) (key.Value base) G) A)
    (path : SourcePrefix (LazyAGM.listOracle (fun sample => respond false (sample, cfg)) (fun sample => respond true (sample, cfg)))
      main initial (queryBind (BLSRecord.request signing message) next) state used) :
    (layout.input default.val signing).valid (message, cfg, state) := by
  have reserved := prefix_reserved layout default P comparison correct response responseBuffers reserve drawSource drawLaw initialReady queries bounded path
  have positive := (path.queryBound bounded).2.1
  have before : Reserved layout ((budget - used - 1) + 1) (cfg, state) := by convert reserved using 1; omega
  apply before.ready default signing message
  have allowed := (path.allowed queries).1
  cases signing <;> exact allowed

end Signatures.Runtime.CaliperBackend.BLSReply
