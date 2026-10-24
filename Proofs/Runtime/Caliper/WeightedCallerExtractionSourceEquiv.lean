import Proofs.Runtime.Caliper.WeightedCallerExtractionSource
import Proofs.Runtime.Caliper.WeightedCallerOriginalSync

/-! Original-key source equality for the complete caller and terminal. Key
transport maps only encountered cache/log entries; it preserves all random
replies and uses the local caller correspondence for the original key domain. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
open Caliper BoundedSource OracleComp OracleSpec
def decodeExtraction {K J M G F R : Type} (decode : K → J)
    (value : (M × (F × (List F × List F))) × (List (K × R) × Model.LazyAGM.Transcript K M G)) :
    (M × (F × (List F × List F))) × (List (J × R) × Model.LazyAGM.Transcript J M G) :=
  (value.1, value.2.1.map (Prod.map decode id), value.2.2.1.map (Prod.map decode id), value.2.2.2)

variable {w : Nat} {C G F M A U : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : Layouts w (key.Value base) M G F (val.Value base) C A)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.service.message
      (GeneratedWeighted.terms layout.service.evaluation layout.terms layout.termCountFits layout.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.service.evaluation.combine layout.service.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.service.responseInput layout.service.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)
    (advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A))
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → layout.forgery.Value ⊕ (layout.Request × A))
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.store.representation.encoding.words < 2 ^ w)
    (fuel : Nat)

variable (source : ProbComp layout.service.evaluation.cache.value.Value)
variable (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (domain : Nat → layout.Request × A → Prop)
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, WeightedCallerHandler.replyMatches layout.service layout.randomBound q represented original →
        WeightedCaller.HeadValid layout.service layout.randomBound domain remaining (advance (c, represented)))
    (admissible : U × layout.service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → WeightedCaller.HeadValid layout.service layout.randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → WeightedOracle.Reserved layout.service layout.terms fuel value.2.val)
    (initialRoom : ∀ value, admissible value → value.2.val.2.1.length + max 1 layout.terms *
      (value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)

variable {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))

variable (fallback : layout.extraction.scalar.Value)
    (extract : layout.extraction.input.Value → ProbComp (WeightedCallerFinish.result layout.extraction).Value)
    (originalExtract : (M × (F × (List F × List F))) ×
      (List (J × val.Value base) × Model.LazyAGM.Transcript J M G) → ProbComp F)
    (extractSource : ∀ value, layout.extraction.ready value →
      (fun answer => answer.val.1) <$> extract value = originalExtract (decodeExtraction keys.symm value.val))

def finishSourceIn (value : Option layout.forgery.Value × WeightedHash.Store J M (val.Value base) C G) : ProbComp F :=
  match value.1 with
  | none => pure fallback.val
  | some forgery => originalExtract (forgery.val, value.2.2)

omit [DecidableEq (key.Value base)] [DecidableEq J] [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include extractSource in
theorem finish_equiv (value : layout.Packet)
    (ready : WeightedCallerFinish.ready layout.extraction layout.extraction.ready (layout.packetView value)) :
    Subtype.val <$> WeightedCallerFinish.denote layout.extraction fallback extract (layout.packetView value) =
      finishSourceIn layout fallback originalExtract (CallerMachine.observe (fun saved : layout.service.store.Value => WeightedOracle.decodeStore keys.symm saved.val) value) := by
  rcases value with ⟨forgery | pending, stored⟩
  · have equality := extractSource
      (WeightedCallerFinish.extractInput layout.extraction
        (forgery, WeightedCallerFinish.storedView layout.extraction layout.config layout.zero layout.default layout.hashPositive layout.signPositive layout.serviceFits stored)) ready
    unfold WeightedCallerFinish.denote WeightedCallerFinish.success
    exact (PFunctor.FreeM.comp_map Subtype.val
      (fun answer : (WeightedCallerFinish.result layout.extraction).Value =>
        (⟨answer.val.1, answer.property.1⟩ : layout.extraction.scalar.Value)) _).symm.trans equality
  · rfl

variable {V : Type}
    (machine : OracleMachine (Model.LazyAGM.advSpec J M G) V layout.forgery.Value)
    (stateView : layout.Request × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ next : (Model.LazyAGM.advSpec J M G).Range
          (WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm q) → machine.State,
        machine.view (stateView (q, c)) = .inr ⟨WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm q, next⟩ →
        ∀ represented original, WeightedCallerHandler.replyMatchesIn layout.service layout.randomBound keys.symm q represented original →
          CallerMachine.Matches machine (WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm) stateView
            (advance (c, represented)) (next original))
    (initialMatches : ∀ value, admissible value →
      CallerMachine.Matches machine (WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm) stateView
        (initial value.1) (machine.init (inputView value.1)))

include combineLaw zeroLaw uniform advanceValid initialValid initialReserved termsEqual advanceMatches initialMatches in
theorem called_equiv
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec J M G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × layout.service.store.Value) (valid : admissible value) :
    CallerMachine.observe (fun saved : layout.service.store.Value => WeightedOracle.decodeStore keys.symm saved.val) <$> called layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source value =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (WeightedCallerHandler.original sourceTerms respond) (sourceProgram (inputView value.1))).run (WeightedOracle.decodeStore keys.symm value.2.val) :=
  CallerMachine.start_eq_simulateQ machine (WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm) stateView
    (fun saved : layout.service.store.Value => WeightedOracle.decodeStore keys.symm saved.val) (WeightedCallerHandler.replyMatchesIn layout.service layout.randomBound keys.symm) advance
    (WeightedCallerHandler.denote layout.service layout.terms layout.termCountFits layout.termStorageFits generator layout.randomBound P comparison correct update updateBuffers updateReserve response source)
    (WeightedCallerHandler.original sourceTerms respond) (WeightedCaller.Invariant layout.service layout.terms layout.randomBound domain)
    (fun _ packet valid => WeightedCallerHandler.synchronizes_equiv layout.service layout.terms layout.termCountFits layout.termStorageFits generator layout.randomBound P comparison correct update updateBuffers updateReserve response
      combineLaw zeroLaw source uniform keys sourceTerms termsEqual (packet.1.1, packet.2)
        (WeightedCallerHandler.ready_of_reserved layout.service layout.terms layout.termCountFits layout.termStorageFits generator layout.randomBound (packet.1.1, packet.2) valid.2))
    (fun remaining q c _ valid => advanceMatches remaining q c valid.1)
    (WeightedCaller.preserves layout.service layout.terms layout.termCountFits layout.termStorageFits generator layout.randomBound P comparison correct update updateBuffers updateReserve response combineLaw zeroLaw source uniform domain advance advanceValid)
    fuel (initial value.1, value.2) (inputView value.1)
    (WeightedCaller.initial_invariant layout.service layout.terms layout.randomBound domain initial fuel admissible initialValid initialReserved value valid)
    (initialMatches value valid) sourceProgram implements

include combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom extractSource termsEqual advanceMatches initialMatches in
theorem denote_equiv
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec J M G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × layout.service.store.Value) (valid : admissible value) :
    Subtype.val <$> denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source fallback extract value =
      ((simulateQ (WeightedCallerHandler.original sourceTerms respond) (sourceProgram (inputView value.1))).run (WeightedOracle.decodeStore keys.symm value.2.val) >>=
        fun answer => originalExtract (answer.1.val, answer.2.2)) := by
  have invoked := called_equiv layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved keys sourceTerms termsEqual machine stateView inputView advanceMatches initialMatches sourceProgram implements value valid
  have finished : Subtype.val <$> denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source fallback extract value =
      (called layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source value >>=
        fun packet => finishSourceIn layout fallback originalExtract (CallerMachine.observe (fun saved : layout.service.store.Value => WeightedOracle.decodeStore keys.symm saved.val) packet)) := by
    simp only [denote, map_bind]
    apply bind_congr_of_forall_mem_support
    intro packet reached
    exact finish_equiv layout keys fallback extract originalExtract extractSource packet
      (called_ready layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source
        admissible initialReserved initialRoom value valid packet reached)
  rw [finished, ← bind_map_left, invoked, bind_map_left]
  rfl

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom extractSource termsEqual advanceMatches initialMatches in
theorem observe_equiv
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn layout.extraction.ready layout.port .unit
      layout.extraction.input.representation (WeightedCallerFinish.result layout.extraction).representation extract extractor)
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec J M G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × layout.service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.store.representation inputFits).Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.extraction.scalar.representation finished) <$>
        (program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).execute layout.port .unit tape before =
      some <$> ((simulateQ (WeightedCallerHandler.original sourceTerms respond) (sourceProgram (inputView value.1))).run (WeightedOracle.decodeStore keys.symm value.2.val) >>=
        fun answer => originalExtract (answer.1.val, answer.2.2)) := by
  have observed := (refines layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel source drawCorrect combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved initialRoom fallback extractCorrect).observe tape value valid before holds
  have equality := denote_equiv layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved initialRoom keys sourceTerms termsEqual fallback extract originalExtract extractSource machine stateView inputView advanceMatches initialMatches
    sourceProgram implements value valid
  have mapped := congrArg (fun computation => (fun answer => Subtype.val <$> answer) <$> computation) observed
  rw [← equality]
  have middle : (fun answer => Subtype.val <$> answer) <$> some <$>
      denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source fallback extract value =
        some <$> Subtype.val <$> denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source fallback extract value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)
end Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
