import Signatures.Runtime.Caliper.WeightedSignFinish
import Signatures.Runtime.WeightedExecution

/-! Complete lazy weighted signing, constructed from the term generator,
cache arithmetic, primitive sampler and local group response. No completed
signing-handler implementation or host-side snapshot is supplied. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSign
open Caliper BoundedSource OracleComp OracleSpec

def decodeOutput {K J M R C G : Type} (decode : K → J) (value : G × Store K M R C G) :
    G × Store J M R C G :=
  (value.1, value.2.1, value.2.2.1.map (Prod.map decode id),
    value.2.2.2.1.map (Prod.map decode id), value.2.2.2.2)

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
    (zero : layout.evaluation.cache.value.Value)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (default : layout.evaluation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots)
    (updateReserve : updateSlots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

def valid (value : layout.input.Value) : Prop :=
  value.val.2.2.1.length + (generate value.val.1).length ≤ layout.evaluation.cache.capacityPred + 1

def evaluator := GeneratedWeighted.code layout.evaluation layout.message capacity countFits storageFits generator
  port default P comparison correct update updateBuffers updateReserve draw
def evaluate : Interactive.Code w :=
  Interactive.retain (evaluator layout capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve port draw)
    (Interactive.savedBuffer port (evaluator layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve port draw))
    layout.evaluationInput.encoding.words layout.evaluated.representation.encoding.words layout.input.representation.encoding.words
def evaluationSource (source : OracleComp spec layout.evaluation.cache.value.Value) :=
  GeneratedWeighted.denote layout.evaluation layout.message capacity countFits storageFits generator
    default P comparison correct update updateBuffers updateReserve source

variable {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {responseSlots : Nat} (responseBuffers : response.program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)

def code : Interactive.Code w :=
  .seq (.compute (prepare layout zero).code)
    (.seq (evaluate layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve port draw)
      (.compute (tail layout response responseBuffers responseReserve).code))
def denote (source : OracleComp spec layout.evaluation.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec layout.output.Value :=
  (fun answer => completed layout response (answer, value)) <$>
    evaluationSource layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve source (argument layout zero value)

variable {source : OracleComp spec layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem refines :
    Interactive.RefinesOn (valid layout (generate := generate)) port .unit layout.input.representation
      layout.output.representation
      (denote layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve response source)
      (code layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve port draw response responseBuffers responseReserve) := by
  have evaluated := (GeneratedWeighted.refines layout.evaluation layout.message capacity countFits storageFits generator
    port layout.evaluationInput.fits default P comparison correct update updateBuffers updateReserve drawCorrect).retain
    (by decide) layout.input.representation layout.evaluation.cache.wordFits layout.prepared.fits layout.post.fits
  have ended := evaluated.seq
    ((Interactive.Refines.compute port .unit (tail layout response responseBuffers responseReserve)).on (fun _ => True))
    (fun _ _ _ _ => trivial)
  have composed := ((Interactive.Refines.compute port .unit (prepare layout zero)).on
    (valid layout (generate := generate))).seq ended (by
      intro value admitted answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact admitted)
  convert composed using 1
  · funext value
    simp only [pure_bind, bind_pure_comp, Functor.map_map, denote, evaluationSource]
    rfl
  · rfl

section Source
variable [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : zero.val = 0)

include combineLaw zeroLaw in
theorem denote_source (source : ProbComp layout.evaluation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (hash : val.Value base → G) (value : layout.input.Value) (admitted : valid layout (generate := generate) value) :
    Subtype.val <$> denote layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve response source value =
      (fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle generate hash (fun scalar => respond (scalar, value.val.2.1))) (.inr value.val.1)).run
          (value.val.2.2.1, value.val.2.2.2) := by
  have evaluated := GeneratedWeighted.evalTerms_source layout.evaluation layout.message capacity countFits storageFits
    generator default P comparison correct update updateBuffers updateReserve combineLaw source uniform
    (argument layout zero value) admitted
  have mapped := congrArg (fun computation : ProbComp (val.Value base × List (key.Value base × val.Value base)) =>
    (fun answer => (respond (answer.1, value.val.2.1), value.val.2.1, answer.2,
      value.val.2.2.2.1, (value.val.1, respond (answer.1, value.val.2.1)) :: value.val.2.2.2.2)) <$> computation) evaluated
  simp only [denote, evaluationSource]
  rw [WeightedAGM.listOracle_sign]
  simp only [Functor.map_map] at mapped ⊢
  simp only [argument, zeroLaw, zero_add] at mapped ⊢
  exact mapped

include combineLaw zeroLaw in
theorem denote_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (source : ProbComp layout.evaluation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (hash : val.Value base → G) (value : layout.input.Value) (admitted : valid layout (generate := generate) value) :
    (fun answer => decodeOutput keys.symm answer.val) <$>
      denote layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve response source value =
      (fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle sourceTerms hash (fun scalar => respond (scalar, value.val.2.1))) (.inr value.val.1)).run
          (value.val.2.2.1.map (Prod.map keys.symm id), value.val.2.2.2.1.map (Prod.map keys.symm id), value.val.2.2.2.2) := by
  have evaluated := GeneratedWeighted.evalTerms_equiv layout.evaluation layout.message capacity countFits storageFits
    generator default P comparison correct update updateBuffers updateReserve combineLaw source uniform
    keys sourceTerms termsEqual (argument layout zero value) admitted
  have mapped := congrArg (fun computation : ProbComp (val.Value base × List (J × val.Value base)) =>
    (fun answer => (respond (answer.1, value.val.2.1), value.val.2.1, answer.2,
      value.val.2.2.2.1.map (Prod.map keys.symm id),
      (value.val.1, respond (answer.1, value.val.2.1)) :: value.val.2.2.2.2)) <$> computation) evaluated
  rw [WeightedAGM.listOracle_sign]
  simp only [denote, evaluationSource, Functor.map_map] at mapped ⊢
  simp only [argument, zeroLaw, zero_add] at mapped ⊢
  exact mapped

include combineLaw zeroLaw in
theorem observe (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (source : ProbComp layout.evaluation.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (hash : val.Value base → G) (tape : RandomTape w)
    (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (before : State w) (holds : layout.input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.output.representation result) <$>
      (code layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve port draw response responseBuffers responseReserve).execute port .unit tape before =
      some <$> ((fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle generate hash (fun scalar => respond (scalar, value.val.2.1))) (.inr value.val.1)).run
          (value.val.2.2.1, value.val.2.2.2)) := by
  have observed := (refines layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve port draw response responseBuffers responseReserve drawCorrect).observe
      tape value admitted before holds
  have mapped := congrArg (fun computation : ProbComp (Option layout.output.Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← denote_source layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve response combineLaw zeroLaw source uniform hash value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

include combineLaw zeroLaw in
theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (source : ProbComp layout.evaluation.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (hash : val.Value base → G) (tape : RandomTape w)
    (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (before : State w) (holds : layout.input.representation.Holds value before) :
    (fun result => (fun answer => decodeOutput keys.symm answer.val) <$>
        Interactive.observe layout.output.representation result) <$>
      (code layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve port draw response responseBuffers responseReserve).execute port .unit tape before =
      some <$> ((fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle sourceTerms hash (fun scalar => respond (scalar, value.val.2.1))) (.inr value.val.1)).run
          (value.val.2.2.1.map (Prod.map keys.symm id), value.val.2.2.2.1.map (Prod.map keys.symm id), value.val.2.2.2.2)) := by
  have observed := (refines layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve port draw response responseBuffers responseReserve drawCorrect).observe
      tape value admitted before holds
  have mapped := congrArg (fun computation : ProbComp (Option layout.output.Value) =>
    (fun result => (fun answer => decodeOutput keys.symm answer.val) <$> result) <$> computation) observed
  rw [← denote_equiv layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve response combineLaw zeroLaw keys sourceTerms termsEqual source uniform hash value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Source
end Signatures.Runtime.CaliperBackend.WeightedSign
