import Signatures.Runtime.Caliper.WeightedCallerOriginal

/-! Coupling for the original-key caller oracle retains both the typed reply
and the entire decoded private store. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerHandler
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets Model.LazyAGM

def replyMatchesIn {w : Nat} {K J M F R C G : Type}
    (layout : WeightedOracle.Layouts w K M F R C G) (randomBound : Nat) (decode : K → J)
    (q : Request layout randomBound) (value : Reply layout randomBound)
    (original : (advSpec J M G).Range (queryIn layout randomBound decode q)) : Prop :=
  replyValue layout randomBound value = answerIn layout randomBound decode q original

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
theorem synchronizes_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (value : Packet layout randomBound) (accepted : ready layout randomBound generate value) :
    Synchronizes (fun represented result => replyMatchesIn layout randomBound keys.symm value.1 represented.1 result.1 ∧
      WeightedOracle.decodeStore keys.symm represented.2.val = result.2)
      (denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source value)
      (((original sourceTerms respond) (queryIn layout randomBound keys.symm value.1)).run
        (WeightedOracle.decodeStore keys.symm value.2.val)) := by
  have joint := Synchronizes.of_map_eq (observedIn layout randomBound keys.symm)
    (fun result : (advSpec J M G).Range (queryIn layout randomBound keys.symm value.1) ×
      WeightedHash.Store J M (val.Value base) C G => (answerIn layout randomBound keys.symm value.1 result.1, result.2))
    (denote_equiv layout capacity countFits storageFits generator randomBound P comparison correct
      update updateBuffers updateReserve response combineLaw zeroLaw source uniform keys sourceTerms termsEqual value accepted)
  exact joint.mono (fun _ _ equal => Prod.mk.inj equal)

end Signatures.Runtime.CaliperBackend.WeightedCallerHandler
