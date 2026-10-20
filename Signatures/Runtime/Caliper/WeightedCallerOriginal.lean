import Signatures.Runtime.Caliper.WeightedCallerSource
import Signatures.Runtime.Caliper.WeightedOracleOriginal

/-! Original-key source correspondence for the caller-facing service. Every
observed random word and the full cache/log state are retained. Only encountered
keys are related through the equivalence; there is no domain enumeration. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerHandler
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets Model.LazyAGM

section Views
variable {w : Nat} {K J M F R C G : Type} (layout : WeightedOracle.Layouts w K M F R C G)
    (randomBound : Nat) (decode : K → J)

def queryIn : Request layout randomBound → (advSpec J M G).Domain
  | .inl n => .inl (.inl n.val)
  | .inr (.inl index) => .inl (.inr (decode index.val))
  | .inr (.inr message) => .inr message.val

def answerIn : (q : Request layout randomBound) → (advSpec J M G).Range (queryIn layout randomBound decode q) → (Nat × Nat) ⊕ G
  | .inl n, value => .inl (n.val, value.val)
  | .inr (.inl _), value | .inr (.inr _), value => .inr value

def observedIn (value : Reply layout randomBound × layout.store.Value) : ((Nat × Nat) ⊕ G) × WeightedHash.Store J M R C G :=
  (replyValue layout randomBound value.1, WeightedOracle.decodeStore decode value.2.val)
end Views

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
theorem denote_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (value : Packet layout randomBound) (accepted : ready layout randomBound generate value) :
    observedIn layout randomBound keys.symm <$>
      denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source value =
      (fun result => (answerIn layout randomBound keys.symm value.1 result.1, result.2)) <$>
        ((original sourceTerms respond) (queryIn layout randomBound keys.symm value.1)).run (WeightedOracle.decodeStore keys.symm value.2.val) := by
  rw [denote, dite_eq_left accepted]
  rcases value with ⟨n | (index | message), saved⟩
  · simp only [serviceRequest, WeightedOracle.denote, Sum.elim_inl, UniformQuery.forwardSource, UniformQuery.source,
      Functor.map_map, queryIn]
    rfl
  · have law := WeightedHash.denote_equiv layout.hashing P comparison correct (response false)
      (fun scalar => respond true (scalar, saved.val.1)) keys sourceTerms source uniform
      ⟨(index.val, saved.val), ⟨index.property, saved.property⟩, accepted⟩
    have mapped := congrArg (fun computation : ProbComp (G × WeightedHash.Store J M (val.Value base) C G) =>
      (fun result => ((Sum.inr result.1 : (Nat × Nat) ⊕ G), result.2)) <$> computation) law
    simp only [serviceRequest, WeightedOracle.denote, WeightedOracle.groupDenote, Sum.elim_inr, Functor.map_map,
      observedIn, finished, replyValue, queryIn, answerIn, original, StateT.run, WeightedOracle.decodeStore] at mapped ⊢
    exact mapped
  · have law := WeightedSign.denote_equiv layout.signing layout.zero capacity countFits storageFits generator layout.default
      P comparison correct update updateBuffers updateReserve (response true) combineLaw zeroLaw keys sourceTerms termsEqual source uniform
      (fun scalar => respond false (scalar, saved.val.1))
      ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, accepted.1⟩ accepted.2
    have mapped := congrArg (fun computation : ProbComp (G × WeightedHash.Store J M (val.Value base) C G) =>
      (fun result => ((Sum.inr result.1 : (Nat × Nat) ⊕ G), result.2)) <$> computation) law
    simp only [serviceRequest, WeightedOracle.denote, WeightedOracle.groupDenote, Sum.elim_inr, Functor.map_map,
      observedIn, finished, replyValue, queryIn, answerIn, original, StateT.run, WeightedOracle.decodeStore] at mapped ⊢
    exact mapped

include combineLaw zeroLaw uniform in
theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation layout.evaluation.cache.value.representation (fun _ => source) draw)
    (tape : RandomTape w) (value : Packet layout randomBound) (accepted : ready layout randomBound generate value)
    (before : State w) (holds : (input layout randomBound randomFits).Holds value before) :
    (fun result => observedIn layout randomBound keys.symm <$> Interactive.observe (output layout randomBound randomFits) result) <$>
      (code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
        update updateBuffers updateReserve draw response responseBuffers responseReserve).execute
          (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit tape before =
      some <$> ((fun result => (answerIn layout randomBound keys.symm value.1 result.1, result.2)) <$>
        ((original sourceTerms respond) (queryIn layout randomBound keys.symm value.1)).run (WeightedOracle.decodeStore keys.symm value.2.val)) := by
  have observed := (refines layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect).observe tape value accepted before holds
  have mapped := congrArg (fun computation : ProbComp (Option (Reply layout randomBound × layout.store.Value)) =>
    (fun result => observedIn layout randomBound keys.symm <$> result) <$> computation) observed
  rw [← denote_equiv layout capacity countFits storageFits generator randomBound P comparison correct
    update updateBuffers updateReserve response combineLaw zeroLaw source uniform keys sourceTerms termsEqual value accepted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Signatures.Runtime.CaliperBackend.WeightedCallerHandler
