import Signatures.Runtime.Caliper.WeightedCallerHandler
import Signatures.Runtime.Caliper.WeightedOracleSource
import Signatures.Runtime.Caliper.SynchronizesObservations

/-! Full source reply/state law for the constructed weighted caller service.
Random reply observations preserve both the requested range and the answer,
so subsequent caller code can inspect all represented reply words. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerHandler
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets Model.LazyAGM

section Observations
variable {w : Nat} {K M F R C G : Type} (layout : WeightedOracle.Layouts w K M F R C G) (randomBound : Nat)

def query : Request layout randomBound → (advSpec K M G).Domain
  | .inl n => .inl (.inl n.val)
  | .inr (.inl message) => .inl (.inr message.val)
  | .inr (.inr message) => .inr message.val

def replyValue : Reply layout randomBound → (Nat × Nat) ⊕ G
  | .inl packet => .inl (packet.1.val, packet.2.val)
  | .inr point => .inr point.val

def answer : (q : Request layout randomBound) → (advSpec K M G).Range (query layout randomBound q) → (Nat × Nat) ⊕ G
  | .inl n, value => .inl (n.val, value.val)
  | .inr (.inl _), value | .inr (.inr _), value => .inr value

def observed (value : Reply layout randomBound × layout.store.Value) : ((Nat × Nat) ⊕ G) × WeightedHash.Store K M R C G :=
  (replyValue layout randomBound value.1, value.2.val)

def replyMatches (q : Request layout randomBound) (value : Reply layout randomBound)
    (original : (advSpec K M G).Range (query layout randomBound q)) : Prop :=
  replyValue layout randomBound value = answer layout randomBound q original

end Observations

section Original
variable {K M F R C G : Type} [DecidableEq K] [SampleableType R] [AddCommMonoid R] [SMul F R]

noncomputable def original (generate : M → List (K × F)) (respond : Bool → R × C → G) :
    QueryImpl (advSpec (K) M G)
      (StateT (WeightedHash.Store (K) M (R) C G) ProbComp) :=
  fun q saved => (fun result => (result.1, saved.1, result.2)) <$>
    ((WeightedAGM.listOracle generate (fun scalar => respond false (scalar, saved.1))
      (fun scalar => respond true (scalar, saved.1))) q).run saved.2

end Original

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : WeightedOracle.Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (source : ProbComp layout.evaluation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw zeroLaw uniform in
theorem denote_source (value : Packet layout randomBound) (accepted : ready layout randomBound generate value) :
    observed layout randomBound <$>
      denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source value =
      (fun result => (answer layout randomBound value.1 result.1, result.2)) <$>
        ((original generate respond) (query layout randomBound value.1)).run value.2.val := by
  rw [denote, dite_eq_left accepted]
  rcases value with ⟨n | (index | message), saved⟩
  · simp only [serviceRequest, WeightedOracle.denote, Sum.elim_inl, UniformQuery.forwardSource, UniformQuery.source,
      Functor.map_map, query]
    rfl
  · have law := WeightedHash.denote_source layout.hashing P comparison correct (response false) generate
      (fun scalar => respond true (scalar, saved.val.1)) source uniform
      ⟨(index.val, saved.val), ⟨index.property, saved.property⟩, accepted⟩
    have mapped := congrArg (fun computation : ProbComp (G × WeightedHash.Store (key.Value base) M (val.Value base) C G) =>
      (fun result => ((Sum.inr result.1 : (Nat × Nat) ⊕ G), result.2)) <$> computation) law
    simp only [serviceRequest, WeightedOracle.denote, WeightedOracle.groupDenote, Sum.elim_inr, Functor.map_map,
      observed, finished, replyValue, query, answer, original, StateT.run] at mapped ⊢
    exact mapped
  · have law := WeightedSign.denote_source layout.signing layout.zero capacity countFits storageFits generator layout.default
      P comparison correct update updateBuffers updateReserve (response true) combineLaw zeroLaw source uniform
      (fun scalar => respond false (scalar, saved.val.1))
      ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, accepted.1⟩ accepted.2
    have mapped := congrArg (fun computation : ProbComp (G × WeightedHash.Store (key.Value base) M (val.Value base) C G) =>
      (fun result => ((Sum.inr result.1 : (Nat × Nat) ⊕ G), result.2)) <$> computation) law
    simp only [serviceRequest, WeightedOracle.denote, WeightedOracle.groupDenote, Sum.elim_inr, Functor.map_map,
      observed, finished, replyValue, query, answer, original, StateT.run] at mapped ⊢
    exact mapped

include combineLaw zeroLaw uniform in
theorem synchronizes (value : Packet layout randomBound) (accepted : ready layout randomBound generate value) :
    Synchronizes (fun represented result => replyMatches layout randomBound value.1 represented.1 result.1 ∧
      represented.2.val = result.2)
      (denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source value)
      (((original generate respond) (query layout randomBound value.1)).run value.2.val) := by
  have joint := Synchronizes.of_map_eq (observed layout randomBound)
    (fun result : (advSpec (key.Value base) M G).Range (query layout randomBound value.1) ×
      WeightedHash.Store (key.Value base) M (val.Value base) C G => (answer layout randomBound value.1 result.1, result.2))
    (denote_source layout capacity countFits storageFits generator randomBound P comparison correct
      update updateBuffers updateReserve response combineLaw zeroLaw source uniform value accepted)
  exact joint.mono (fun _ _ equal => Prod.mk.inj equal)

end Signatures.Runtime.CaliperBackend.WeightedCallerHandler
