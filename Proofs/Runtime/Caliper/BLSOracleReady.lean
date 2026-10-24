import Proofs.Runtime.Caliper.BLSOracleSource

/-! The original source query and its reachable private state determine a valid
service input. These are representation proofs, not uncharged input-building
instructions. A caller still has to place the encoded packet in machine memory. -/

namespace Signatures.Runtime.CaliperBackend.BLSOracle
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM

section Requests
variable {w : Nat} {M R C G : Type} [DecidableEq M]
    (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value) (randomBound : Nat)

def allowed : (advSpec M M G).Domain → Prop
  | .inl (.inl n) => n ≤ randomBound
  | .inl (.inr message) | .inr message => layout.cache.key.valid message

omit [DecidableEq M] in
theorem allowed_message (q : (advSpec M M G).Domain) (valid : allowed layout randomBound q) :
    BLSRecord.allowedQuery layout.records q := by
  rcases q with ((n | message) | message)
  · trivial
  · exact valid
  · exact valid

omit [DecidableEq M] in
theorem allowed_messages {A : Type} {main : OracleComp (advSpec M M G) A}
    (queries : AllQueriesSatisfy main (allowed layout randomBound)) :
    AllQueriesSatisfy main (BLSRecord.allowedQuery layout.records) := by
  induction main using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind q next ih => exact ⟨allowed_message layout randomBound q queries.1, fun reply => ih reply (queries.2 reply)⟩

def stored {remaining : Nat} {value : BLSReply.Store M R C G} (reserved : BLSReply.Reserved layout remaining value) : layout.store.Value :=
  ⟨value, reserved.config,
    ⟨by change value.2.1.length ≤ layout.cache.capacityPred + 1; have := reserved.cacheRoom; omega, reserved.cached⟩,
    ⟨by change value.2.2.1.length ≤ layout.capacityPred + 1; have := reserved.logRoom; omega, reserved.recorded.1⟩,
    ⟨by change value.2.2.2.length ≤ layout.capacityPred + 1; have := reserved.logRoom; omega, reserved.recorded.2⟩⟩

def request {remaining : Nat} {value : BLSReply.Store M R C G}
    (reserved : BLSReply.Reserved layout (remaining + 1) value)
    (q : (advSpec M M G).Domain) (valid : allowed layout randomBound q) :
    (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value :=
  match q with
  | .inl (.inl n) => .inl (⟨n, Nat.lt_succ_of_le valid⟩, stored layout reserved)
  | .inl (.inr message) => .inr (BLSDispatch.request layout default false
      ⟨(message, value), reserved.ready default false message valid⟩)
  | .inr message => .inr (BLSDispatch.request layout default true
      ⟨(message, value), reserved.ready default true message valid⟩)

theorem query_request {remaining : Nat} {value : BLSReply.Store M R C G}
    (reserved : BLSReply.Reserved layout (remaining + 1) value)
    (q : (advSpec M M G).Domain) (valid : allowed layout randomBound q) :
    query layout default randomBound (request layout default randomBound reserved q valid) = q := by
  rcases q with ((n | message) | message) <;> rfl

theorem saved_request {remaining : Nat} {value : BLSReply.Store M R C G}
    (reserved : BLSReply.Reserved layout (remaining + 1) value)
    (q : (advSpec M M G).Domain) (valid : allowed layout randomBound q) :
    saved layout default randomBound (request layout default randomBound reserved q valid) = value := by
  rcases q with ((n | message) | message) <;> rfl
end Requests

variable {w : Nat} {C G : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (randomBound : Nat)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (drawSource : ProbComp layout.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include default P comparison correct response responseBuffers reserve drawLaw in
theorem prefix_ready {A : Type} {main : OracleComp (advSpec (key.Value base) (key.Value base) G) A}
    {cfg : C} {initial state : LazyAGM.State (key.Value base) (val.Value base) G} {used budget : Nat}
    (initialReady : BLSReply.Reserved layout budget (cfg, initial))
    (queries : AllQueriesSatisfy main (allowed layout randomBound)) (bounded : IsTotalQueryBound main budget)
    (q : (advSpec (key.Value base) (key.Value base) G).Domain)
    (next : (advSpec (key.Value base) (key.Value base) G).Range q → OracleComp (advSpec (key.Value base) (key.Value base) G) A)
    (path : SourcePrefix (LazyAGM.listOracle (fun sample => respond false (sample, cfg)) (fun sample => respond true (sample, cfg)))
      main initial (queryBind q next) state used) :
    ∃ value : (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value,
      query layout default randomBound value = q ∧ saved layout default randomBound value = (cfg, state) := by
  have reserved := BLSReply.prefix_reserved layout default P comparison correct response responseBuffers reserve drawSource drawLaw
    initialReady (allowed_messages layout randomBound queries) bounded path
  have positive := (path.queryBound bounded).2.1
  have before : BLSReply.Reserved layout ((budget - used - 1) + 1) (cfg, state) := by convert reserved using 1; omega
  have valid := (path.allowed queries).1
  exact ⟨request layout default randomBound before q valid,
    query_request layout default randomBound before q valid, saved_request layout default randomBound before q valid⟩

end Signatures.Runtime.CaliperBackend.BLSOracle
