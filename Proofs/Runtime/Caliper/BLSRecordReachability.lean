import Proofs.Runtime.Caliper.BLSRecordLayout
import Proofs.Runtime.Caliper.SourcePrefix
import Proofs.Runtime.LazyAGMExecution

/-! The transcript insertion domain follows from the original lazy source
oracle's reachable prefixes and query allowance. Repeated delivered replies each
occupy a slot; private cache entries and private randomness do not create tokens. -/

namespace Signatures.Runtime.CaliperBackend.BLSRecord

open BoundedSource OracleComp OracleSpec Model.LazyAGM

variable {w : Nat} {M G R A : Type} [DecidableEq M] [SampleableType R]
    (layout : Layouts w M G)

def allowedQuery : (advSpec M M G).Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr message) | .inr message => layout.message.valid message

def entriesFit (tr : Transcript M G) : Prop :=
  (∀ entry ∈ tr.1, layout.entry.valid entry) ∧ (∀ entry ∈ tr.2, layout.entry.valid entry)

omit [DecidableEq M] in
theorem record_entries (signing : Bool) (message : M) (reply : G) (tr : Transcript M G)
    (messageFits : layout.message.valid message) (replyFits : layout.point.valid reply) (valid : entriesFit layout tr) :
    entriesFit layout (LazyAGM.record signing message reply tr) := by
  have entryFits : layout.entry.valid (message, reply) := ⟨messageFits, replyFits⟩
  cases signing
  · exact ⟨by intro entry member; rcases List.mem_cons.mp member with rfl | member
              · exact entryFits
              · exact valid.1 entry member,
      valid.2⟩
  · exact ⟨valid.1, by intro entry member; rcases List.mem_cons.mp member with rfl | member
                       · exact entryFits
                       · exact valid.2 entry member⟩

theorem reply_entries (signing : Bool) (response : R → G) (responseFits : ∀ value, layout.point.valid (response value))
    (message : M) (messageFits : layout.message.valid message) (state : LazyAGM.State M R G)
    (valid : entriesFit layout state.2) (out : G × LazyAGM.State M R G)
    (supported : out ∈ support ((LazyAGM.listReply signing response message).run state)) :
    entriesFit layout out.2.2 := by
  simp only [LazyAGM.listReply, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨value, _, rfl⟩ := supported
  exact record_entries layout signing message _ state.2 messageFits (responseFits value.1) valid

variable (hash sign : R → G) (hashFits : ∀ value, layout.point.valid (hash value)) (signFits : ∀ value, layout.point.valid (sign value))

include hashFits signFits in
theorem query_entries (query : (advSpec M M G).Domain) (allowed : allowedQuery layout query)
    (state : LazyAGM.State M R G) (valid : entriesFit layout state.2)
    (out : (advSpec M M G).Range query × LazyAGM.State M R G)
    (supported : out ∈ support ((LazyAGM.listOracle hash sign query).run state)) : entriesFit layout out.2.2 := by
  rcases query with ((n | message) | message)
  · rw [LazyAGM.listOracle_random] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    exact valid
  · exact reply_entries layout false hash hashFits message allowed state valid out supported
  · exact reply_entries layout true sign signFits message allowed state valid out supported

include hashFits signFits in
theorem prefix_entries {main residual : OracleComp (advSpec M M G) A} {initial state : LazyAGM.State M R G} {used : Nat}
    (queries : AllQueriesSatisfy main (allowedQuery layout)) (valid : entriesFit layout initial.2)
    (path : SourcePrefix (LazyAGM.listOracle hash sign) main initial residual state used) : entriesFit layout state.2 := by
  induction path with
  | start => exact valid
  | step path answer supported ih =>
    exact query_entries layout hash sign hashFits signFits _ (path.allowed queries).1 _ ih answer supported

def request (signing : Bool) (message : M) : (advSpec M M G).Domain :=
  if signing then .inr message else .inl (.inr message)

include hashFits signFits in
/-- Before a delivered query, every represented reply can be recorded. The
allowance bounds encountered replies, without bounding the message universe. -/
theorem ready {main : OracleComp (advSpec M M G) A} {initial state : LazyAGM.State M R G} {used budget : Nat}
    (queries : AllQueriesSatisfy main (allowedQuery layout)) (valid : entriesFit layout initial.2)
    (bounded : IsTotalQueryBound main budget)
    (capacity : initial.2.1.length + initial.2.2.length + budget ≤ layout.capacityPred + 1)
    (signing : Bool) (message : M) (next : (advSpec M M G).Range (request (G := G) signing message) → OracleComp (advSpec M M G) A)
    (path : SourcePrefix (LazyAGM.listOracle hash sign) main initial
      (queryBind (request signing message) next) state used)
    (reply : G) (replyFits : layout.point.valid reply) : (layout.input signing).valid ((message, reply), state.2) := by
  have limits := path.queryBound bounded
  have remaining := limits.2.1
  have growth := path.growth (fun state : LazyAGM.State M R G => state.2.1.length + state.2.2.length)
    (fun query state answer supported => (LazyAGM.listOracle_growth hash sign query state answer supported).2)
  have stored := prefix_entries layout hash sign hashFits signFits queries valid path
  have messageFits : layout.message.valid message := by
    have allowed := (path.allowed queries).1
    cases signing <;> exact allowed
  change ((layout.message.valid message ∧ layout.point.valid reply) ∧
    (state.2.1.length ≤ layout.capacityPred + 1 ∧ _) ∧ (state.2.2.length ≤ layout.capacityPred + 1 ∧ _)) ∧ _
  refine ⟨⟨⟨messageFits, replyFits⟩, ⟨by omega, stored.1⟩, ⟨by omega, stored.2⟩⟩, ?_⟩
  cases signing <;> simp only [Layouts.room, Bool.false_eq_true, ↓reduceIte] <;> omega

end Signatures.Runtime.CaliperBackend.BLSRecord
