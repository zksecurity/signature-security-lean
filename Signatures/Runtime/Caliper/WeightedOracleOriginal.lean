import Signatures.Runtime.Caliper.WeightedOracleSource

/-! Recover the original game index type for the entire executed service.
The relation maps encountered cache/log keys and never enumerates a domain. -/
namespace Signatures.Runtime.CaliperBackend.WeightedOracle
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM

section Views
variable {w : Nat} {K J M F R C G : Type} [DecidableEq K]
    (layout : Layouts w K M F R C G) (randomBound : Nat) (decode : K → J)
def decodeStore (store : WeightedHash.Store K M R C G) : WeightedHash.Store J M R C G :=
  (store.1, store.2.1.map (Prod.map decode id), store.2.2.1.map (Prod.map decode id), store.2.2.2)
def queryIn : Input layout randomBound → (advSpec J M G).Domain
  | .inl value => .inl (.inl value.1.val)
  | .inr (.inl value) => .inl (.inr (decode value.val.1))
  | .inr (.inr value) => .inr value.val.1
def decodedIn (value : Output layout randomBound) : (Nat ⊕ G) × WeightedHash.Store J M R C G :=
  ((decoded layout randomBound value).1, decodeStore decode (decoded layout randomBound value).2)
end Views

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
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
    (value : Input layout randomBound) (admitted : valid layout (generate := generate) randomBound value) :
    decodedIn layout randomBound keys.symm <$>
      denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source value =
      (fun result => (answer (queryIn layout randomBound keys.symm value) result.1, (saved layout randomBound value).1, result.2)) <$>
        ((WeightedAGM.listOracle sourceTerms
          (fun scalar => respond false (scalar, (saved layout randomBound value).1))
          (fun scalar => respond true (scalar, (saved layout randomBound value).1)))
          (queryIn layout randomBound keys.symm value)).run (decodeStore keys.symm (saved layout randomBound value)).2 := by
  rcases value with random | (hashed | signed)
  · simp only [denote, Sum.elim_inl, UniformQuery.forwardSource, UniformQuery.source, Functor.map_map,
      queryIn, saved, WeightedAGM.listOracle_random]
    rfl
  · have law := WeightedHash.denote_equiv layout.hashing P comparison correct (response false)
      (fun scalar => respond true (scalar, hashed.val.2.1)) keys sourceTerms source uniform hashed
    have mapped := congrArg (fun computation : ProbComp (G × WeightedHash.Store J M (val.Value base) C G) =>
      (fun result => ((Sum.inr result.1 : Nat ⊕ G), result.2)) <$> computation) law
    simp only [denote, groupDenote, Sum.elim_inr, Functor.map_map, decodedIn, decoded, decodeStore, queryIn, saved, answer] at mapped ⊢
    exact mapped
  · have law := WeightedSign.denote_equiv layout.signing layout.zero capacity countFits storageFits generator layout.default
      P comparison correct update updateBuffers updateReserve (response true) combineLaw zeroLaw keys sourceTerms termsEqual source uniform
      (fun scalar => respond false (scalar, signed.val.2.1)) signed admitted
    have mapped := congrArg (fun computation : ProbComp (G × WeightedHash.Store J M (val.Value base) C G) =>
      (fun result => ((Sum.inr result.1 : Nat ⊕ G), result.2)) <$> computation) law
    simp only [denote, groupDenote, Sum.elim_inr, Functor.map_map, decodedIn, decoded, decodeStore, queryIn, saved, answer] at mapped ⊢
    exact mapped

include combineLaw zeroLaw uniform in
theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation layout.evaluation.cache.value.representation (fun _ => source) draw)
    (tape : RandomTape w) (value : Input layout randomBound) (admitted : valid layout (generate := generate) randomBound value)
    (before : State w) (holds : (layout.input randomBound randomFits).Holds value before) :
    (fun result => decodedIn layout randomBound keys.symm <$> Interactive.observe (layout.output randomBound randomFits) result) <$>
      (code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
        update updateBuffers updateReserve draw response responseBuffers responseReserve).execute
          (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit tape before =
      some <$> ((fun result => (answer (queryIn layout randomBound keys.symm value) result.1, (saved layout randomBound value).1, result.2)) <$>
        ((WeightedAGM.listOracle sourceTerms
          (fun scalar => respond false (scalar, (saved layout randomBound value).1))
          (fun scalar => respond true (scalar, (saved layout randomBound value).1)))
          (queryIn layout randomBound keys.symm value)).run (decodeStore keys.symm (saved layout randomBound value)).2) := by
  have observed := (refines layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect).observe tape value admitted before holds
  have mapped := congrArg (fun computation : ProbComp (Option (Output layout randomBound)) =>
    (fun result => decodedIn layout randomBound keys.symm <$> result) <$> computation) observed
  rw [← denote_equiv layout capacity countFits storageFits generator randomBound P comparison correct
    update updateBuffers updateReserve response combineLaw zeroLaw source uniform keys sourceTerms termsEqual value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Signatures.Runtime.CaliperBackend.WeightedOracle
