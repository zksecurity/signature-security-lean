import Proofs.Runtime.Caliper.BLSCallerExtraction

/-! Source equality for the composed caller and extraction. Local machine-head
correspondence supplies the original adversary semantics. Extraction equality
is local to admitted forgeries/stores, and the caller growth proof supplies that
domain on every supported exit. ImplementsWithin excludes cutoff. -/
namespace Signatures.Runtime.CaliperBackend.BLSCallerExtraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {C G F A U : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : Layouts w (key.Value base) G F (val.Value base) C A)
    (default : layout.service.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.service.responseInput layout.service.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)
    (advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A))
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → layout.forgery.Value ⊕ (layout.Request × A))
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.store.representation.encoding.words < 2 ^ w)
    (fuel : Nat)

variable (drawSource : ProbComp layout.service.cache.value.Value)
variable (drawCorrect : Interactive.Refines layout.port .unit layout.service.cache.lookup.unit.representation layout.service.cache.value.representation
      (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (domain : Nat → layout.Request × A → Prop)
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, BLSCallerHandler.replyMatches layout.service layout.randomBound q represented original →
        BLSCaller.HeadValid layout.service layout.randomBound domain remaining (advance (c, represented)))
    (admissible : U × layout.service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → BLSCaller.HeadValid layout.service layout.randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → BLSReply.Reserved layout.service fuel value.2.val)
    (initialRoom : ∀ value, admissible value → value.2.val.2.1.length + value.2.val.2.2.1.length +
      value.2.val.2.2.2.length + 2 * fuel + 1 ≤ layout.service.cache.capacityPred + 1)

variable (fallback : layout.extraction.rows.accumulation.coefficient.Value)
    (extract : (BLSExtractorFrame.input layout.extraction).Value → ProbComp (BLSCallerFinish.result layout.extraction).Value)
    (originalExtract : (key.Value base × (F × (List F × List F))) ×
      (List (key.Value base × val.Value base) × Model.LazyAGM.Transcript (key.Value base) (key.Value base) G) → ProbComp F)
    (extractSource : ∀ value, BLSExtractorFrame.ready layout.extraction value →
      (fun answer => answer.val.1) <$> extract value = originalExtract value.val)

def finishSource (value : Option layout.forgery.Value × BLSReply.Store (key.Value base) (val.Value base) C G) : ProbComp F :=
  match value.1 with
  | none => pure fallback.val
  | some forgery => originalExtract (forgery.val, value.2.2)

omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)] in
include extractSource in
theorem finish_source (value : layout.Packet)
    (ready : BLSCallerFinish.ready layout.extraction (BLSExtractorFrame.ready layout.extraction) (layout.packetView value)) :
    Subtype.val <$> BLSCallerFinish.denote layout.extraction fallback extract (layout.packetView value) =
      finishSource layout fallback originalExtract (CallerMachine.observe Subtype.val value) := by
  rcases value with ⟨forgery | pending, stored⟩
  · have equality := extractSource
      (BLSCallerFinish.extractInput layout.extraction
        (forgery, BLSCallerFinish.storedView layout.extraction layout.config layout.positive layout.serviceFits stored)) ready
    unfold BLSCallerFinish.denote BLSCallerFinish.success
    exact (PFunctor.FreeM.comp_map Subtype.val
      (fun answer : (BLSCallerFinish.result layout.extraction).Value =>
        (⟨answer.val.1, answer.property.1⟩ : layout.extraction.rows.accumulation.coefficient.Value)) _).symm.trans equality
  · rfl

variable {V : Type}
    (machine : OracleMachine (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) V layout.forgery.Value)
    (stateView : layout.Request × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ next : (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G).Range
          (BLSCallerHandler.query layout.service layout.randomBound q) → machine.State,
        machine.view (stateView (q, c)) = .inr ⟨BLSCallerHandler.query layout.service layout.randomBound q, next⟩ →
        ∀ represented original, BLSCallerHandler.replyMatches layout.service layout.randomBound q represented original →
          CallerMachine.Matches machine (BLSCallerHandler.query layout.service layout.randomBound) stateView
            (advance (c, represented)) (next original))
    (initialMatches : ∀ value, admissible value →
      CallerMachine.Matches machine (BLSCallerHandler.query layout.service layout.randomBound) stateView
        (initial value.1) (machine.init (inputView value.1)))

include drawLaw advanceValid initialValid initialReserved advanceMatches initialMatches in
theorem called_source
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × layout.service.store.Value) (valid : admissible value) :
    CallerMachine.observe Subtype.val <$> called layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource value =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (BLSCallerHandler.original respond) (sourceProgram (inputView value.1))).run value.2.val :=
  CallerMachine.start_eq_simulateQ machine (BLSCallerHandler.query layout.service layout.randomBound) stateView
    Subtype.val (BLSCallerHandler.replyMatches layout.service layout.randomBound) advance
    (BLSCallerHandler.denote layout.service default layout.randomBound P comparison correct response responseBuffers reserve drawSource)
    (BLSCallerHandler.original respond) (BLSCaller.Invariant layout.service layout.randomBound domain)
    (fun _ packet valid => BLSCallerHandler.synchronizes layout.service default layout.randomBound P comparison correct response responseBuffers reserve
      drawSource drawLaw (packet.1.1, packet.2)
        (BLSCallerHandler.ready_of_reserved layout.service default layout.randomBound (packet.1.1, packet.2) valid.2))
    (fun remaining q c _ valid => advanceMatches remaining q c valid.1)
    (BLSCaller.preserves layout.service default layout.randomBound P comparison correct response responseBuffers reserve drawSource drawLaw domain advance advanceValid)
    fuel (initial value.1, value.2) (inputView value.1)
    (BLSCaller.initial_invariant layout.service layout.randomBound domain initial fuel admissible initialValid initialReserved value valid)
    (initialMatches value valid) sourceProgram implements

include drawLaw advanceValid initialValid initialReserved initialRoom extractSource advanceMatches initialMatches in
theorem denote_source
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × layout.service.store.Value) (valid : admissible value) :
    Subtype.val <$> denote layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource fallback extract value =
      ((simulateQ (BLSCallerHandler.original respond) (sourceProgram (inputView value.1))).run value.2.val >>=
        fun answer => originalExtract (answer.1.val, answer.2.2)) := by
  have invoked := called_source layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource drawLaw domain advanceValid
    admissible initialValid initialReserved machine stateView inputView advanceMatches initialMatches sourceProgram implements value valid
  have finished : Subtype.val <$> denote layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource fallback extract value =
      (called layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource value >>=
        fun packet => finishSource layout fallback originalExtract (CallerMachine.observe Subtype.val packet)) := by
    simp only [denote, map_bind]
    apply bind_congr_of_forall_mem_support
    intro packet reached
    exact finish_source layout fallback extract originalExtract extractSource packet
      (called_ready layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource drawLaw
        admissible initialReserved initialRoom value valid packet reached)
  rw [finished, ← bind_map_left, invoked, bind_map_left]
  rfl

include drawCorrect drawLaw advanceValid initialValid initialReserved initialRoom extractSource advanceMatches initialMatches in
theorem observe_source
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn (BLSExtractorFrame.ready layout.extraction) layout.port .unit
      (BLSExtractorFrame.input layout.extraction).representation (BLSCallerFinish.result layout.extraction).representation extract extractor)
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × layout.service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.store.representation inputFits).Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.extraction.rows.accumulation.coefficient.representation finished) <$>
        (program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).execute layout.port .unit tape before =
      some <$> ((simulateQ (BLSCallerHandler.original respond) (sourceProgram (inputView value.1))).run value.2.val >>=
        fun answer => originalExtract (answer.1.val, answer.2.2)) := by
  have observed := (refines layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel drawSource drawCorrect drawLaw domain advanceValid
    admissible initialValid initialReserved initialRoom fallback extractCorrect).observe tape value valid before holds
  have equality := denote_source layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource drawLaw domain advanceValid
    admissible initialValid initialReserved initialRoom fallback extract originalExtract extractSource machine stateView inputView advanceMatches initialMatches
    sourceProgram implements value valid
  have mapped := congrArg (fun computation => (fun answer => Subtype.val <$> answer) <$> computation) observed
  rw [← equality]
  have middle : (fun answer => Subtype.val <$> answer) <$> some <$>
      denote layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource fallback extract value =
        some <$> Subtype.val <$> denote layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource fallback extract value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)
end Signatures.Runtime.CaliperBackend.BLSCallerExtraction
