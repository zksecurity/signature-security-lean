import Proofs.Runtime.Caliper.WeightedCallerProgramResources
import Proofs.Runtime.Caliper.WeightedCallerReduction
import Proofs.Runtime.Caliper.WeightedInitialization
import Proofs.Runtime.Caliper.WeightedGood
import Proofs.Runtime.Caliper.WeightedBad
import Proofs.Runtime.Caliper.OOPSTermsBounds
import Proofs.Runtime.Caliper.BLSExtractArithmeticNames
import Proofs.Runtime.Caliper.BLSResponseNames
import Proofs.Runtime.Caliper.UniformSamplingBounds
import Mathlib.Data.BitVec
import Lean

/-! Execute a generated weighted caller through its actual terminal dispatcher
and extractor. Word arithmetic exercises code, not a field security model. -/
namespace SignaturesTest.CaliperWeightedCaller
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
private def scalar : Layout 32 (Word 32) := Layout.all (wordRepresentation 32 (by decide))
private def oops : OOPSTerms.Layouts 32 (Word 32) (Word 32) 1 :=
  ⟨scalar, scalar, by decide, by decide, by decide⟩
private abbrev Key := Fin 2 × Word 32
private def base : Bool → Type
  | false => Key
  | true => Word 32
private instance : DecidableEq (Ty.Value base (.atom false)) := inferInstanceAs (DecidableEq Key)
private instance (n : Nat) : OfNat (Ty.Value base (.atom true)) n := inferInstanceAs (OfNat (Word 32) n)
private inductive Op : Ty Bool → Ty Bool → Type
  | equal : Op (.pair (.atom false) (.atom false)) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with
    | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.atom false, .atom false] .bool :=
  .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Key) :
    comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def accumulation : BLSPrivateAccumulate.Layouts 32 Key (Word 32) where
  cache := {
    key := oops.terms.key
    value := scalar
    capacityPred := 5
    wordFits := by decide
    countFits := by decide
    storageFits := by decide }
  pairStorageFits := by decide
  scalarStorageFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide

private def binary (op : BinOp) : Implementation .unit accumulation.arithmetic.pair scalar
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op (by decide)).viewInput accumulation.arithmetic.pair.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput scalar.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def mul := binary .mul
private def add := binary .add
private theorem mulBound : mul.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem addBound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem mulNames : NamesBound mul.program.code 3 := ⟨by decide, by decide⟩
private theorem addNames : NamesBound add.program.code 3 := ⟨by decide, by decide⟩
private def goodUpdate := BLSPrivateAccumulate.goodUpdate accumulation mul add mulNames.buffers (by decide)
private def badUpdate := BLSPrivateAccumulate.badUpdate accumulation mul add mulNames.buffers (by decide) addNames.buffers
private theorem goodBuffers : goodUpdate.program.code.memBound ≤ 4 :=
  BLSPrivateAccumulate.goodUpdate_buffers accumulation mul add mulNames.buffers (by decide) addNames.buffers
private theorem badBuffers : badUpdate.program.code.memBound ≤ 5 :=
  BLSPrivateAccumulate.badUpdate_buffers accumulation mul add mulNames.buffers (by decide) addNames.buffers
private def oopsGenerator := OOPSTerms.implementation oops trivial mul mulNames.buffers (by decide)
private theorem oopsBound : oopsGenerator.BoundedBy (OOPSTerms.timeBudget oops 6) (OOPSTerms.codeBudget oops 27) :=
  OOPSTerms.bounded oops trivial mul mulNames.buffers (by decide) mulBound
private theorem oopsNames : NamesAccounted oopsGenerator.program.code 3 :=
  OOPSTerms.names oops trivial mul mulNames.buffers (by decide) mulNames.accounted
private theorem goodBound : goodUpdate.BoundedBy
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6) (BLSAccumulate.goodCode accumulation.arithmetic 27 27) :=
  BLSAccumulate.good_bounded accumulation.arithmetic mul add mulBound addBound mulNames.buffers (by decide)
private theorem goodNames : NamesAccounted goodUpdate.program.code 3 :=
  BLSAccumulate.good_names accumulation.arithmetic 3 mul add mulNames.accounted addNames.accounted mulNames.buffers (by decide)

private instance : SampleableType (Word 32) :=
  SampleableType.ofEquiv BitVec.equivFin.toEquiv.symm
private instance : SampleableType (Ty.Value base (.atom true)) :=
  inferInstanceAs (SampleableType (Word 32))
private instance : AddCommMonoid (Ty.Value base (.atom true)) :=
  inferInstanceAs (AddCommMonoid (Word 32))
private instance : SMul (Word 32) (Ty.Value base (.atom true)) :=
  inferInstanceAs (SMul (Word 32) (Word 32))

private def uniformPort := UniformQuery.port (w := 32) 4294967295 (by decide) (by decide)
private def uniformDraw := UniformSampling.code (w := 32) 4294967295 (by decide) (by decide) 4294967295
private def uniformSource : ProbComp scalar.Value :=
  (fun value => (⟨BitVec.ofFin value.val, trivial⟩ : scalar.Value)) <$>
    UniformSampling.source (w := 32) 4294967295 (by decide) (by decide) 4294967295
private theorem uniformCorrect : Interactive.Refines uniformPort .unit
    accumulation.cache.lookup.unit.representation scalar.representation (fun _ => uniformSource) uniformDraw :=
  (UniformSampling.refines (w := 32) 4294967295 (by decide) (by decide) 4294967295).viewOutput
    scalar.representation (fun value => ⟨BitVec.ofFin value.val, trivial⟩) (by
      intro value
      change [BitVec.ofFin value.val] = [BitVec.ofNat 32 value.val.val]
      congr 1
      apply BitVec.eq_of_toNat_eq
      exact (Nat.mod_eq_of_lt value.val.isLt).symm)
private theorem uniformLaw :
    Subtype.val <$> uniformSource = ($ᵗ (Ty.Value base (.atom true)) : ProbComp _) := by
  simp only [uniformSource, UniformSampling.source, Functor.map_map]
  rfl

private def sub := binary .sub
private def divide := binary .udiv
private def scalarZero : Implementation .unit scalar scalar (fun _ => 0) :=
  Implementation.constant scalar scalar ⟨0, trivial⟩ accumulation.cache.wordFits
private def negArgs : Implementation .unit scalar accumulation.arithmetic.pair (fun value => (0, value)) :=
  scalarZero.pair (Implementation.identity scalar (by decide)) (by decide) accumulation.cache.wordFits
    (by decide) (by decide) (by decide) (by decide) accumulation.arithmetic.pair.representation.fits
private def negate : Implementation .unit scalar scalar Neg.neg :=
  (negArgs.then sub).castFunction (by funext value; exact BitVec.zero_sub value)
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem divBound : divide.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem negBound : negate.BoundedBy 118 631 := by
  have zeroBound := Implementation.constant_bounded scalar scalar ⟨0, trivial⟩ accumulation.cache.wordFits
  have paired : negArgs.BoundedBy 112 603 := by
    apply (Implementation.pair_boundedBy scalarZero (Implementation.identity scalar (by decide))
      accumulation.cache.wordFits (by decide) (by decide) (by decide) (by decide)
      accumulation.arithmetic.pair.representation.fits
      zeroBound (Implementation.identity_boundedBy scalar (by decide))).mono <;> decide
  apply ((paired.then subBound).castFunction _).mono <;> decide
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private theorem divNames : NamesBound divide.program.code 3 := ⟨by decide, by decide⟩
private theorem negNames : NamesBound negate.program.code 3 := ⟨by decide, by decide⟩
private def goodExtract := BLSExtractArithmetic.good accumulation.arithmetic sub subNames.buffers (by decide) divide
private def badExtract := BLSExtractArithmetic.bad accumulation.arithmetic sub subNames.buffers (by decide)
  negate negNames.buffers divide
private theorem goodExtractBuffers : goodExtract.program.code.memBound ≤ 4 :=
  BLSExtractArithmetic.good_buffers accumulation.arithmetic sub subNames.buffers (by decide) divide divNames.buffers
private theorem badExtractBuffers : badExtract.program.code.memBound ≤ 4 :=
  BLSExtractArithmetic.bad_buffers accumulation.arithmetic sub subNames.buffers (by decide)
    negate negNames.buffers divide divNames.buffers
private theorem goodExtractBound : goodExtract.BoundedBy
    (BLSExtractArithmetic.goodTime accumulation.arithmetic 6 6)
    (BLSExtractArithmetic.goodCode accumulation.arithmetic 27 27) :=
  BLSExtractArithmetic.good_bounded accumulation.arithmetic sub subBound subNames.buffers (by decide) divide divBound
private theorem badExtractBound : badExtract.BoundedBy
    (BLSExtractArithmetic.badTime accumulation.arithmetic 6 118 6)
    (BLSExtractArithmetic.badCode accumulation.arithmetic 27 631 27) :=
  BLSExtractArithmetic.bad_bounded accumulation.arithmetic sub subBound subNames.buffers (by decide)
    negate negBound negNames.buffers divide divBound
private theorem goodExtractNames : NamesAccounted goodExtract.program.code 3 :=
  BLSExtractArithmetic.good_names accumulation.arithmetic 3 sub subNames.accounted subNames.buffers
    (by decide) divide divNames.accounted
private def executeUniform {A B : Type} (input : Representation 32 A) (output : Layout 32 B)
    (code : Interactive.Code 32) (value : A) (replies : List (Word 32)) := do
  let initial := input.initial value
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 4 else initial.caps buffer
    regs := fun register => if register = 99 then 91 else initial.regs register
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (code.lower uniformPort) before replies
  let answer ← output.representation.encoding.decode (result.state.bufs 0).toList
  pure (answer.val, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 40).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining, result.time)


private def signing : WeightedExtraction.Layouts 32 Key (Word 32 × Word 32) (Word 32) (Word 32) (Word 32) :=
  ⟨⟨⟨accumulation.good, oops.input, by decide⟩, scalar, by decide⟩,
    3, 4, 2, by decide, by decide, by decide, by decide, by decide⟩
private def extraction : WeightedExtractor.Layouts 32 Key (Word 32 × Word 32) (Word 32) (Word 32) (Word 32) :=
  ⟨signing, 2, 3, by decide, by decide, by decide⟩
private def layout : WeightedCallerExtraction.Layouts 32 Key (Word 32 × Word 32) (Word 32) (Word 32) (Word 32)
    (Word 32) extraction.forgery.Value where
  extraction := extraction
  config := scalar
  zero := ⟨0, trivial⟩
  default := ⟨99, trivial⟩
  hashPositive := by decide
  signPositive := by decide
  serviceFits := by decide
  randomBound := 4294967295
  randomFits := by decide
  state := extraction.forgery.representation
  callerFits := by decide
private def response (_ : Bool) : Implementation .unit layout.service.responseInput scalar (fun value => value.1) :=
  Implementation.first (by decide) scalar scalar (by decide) (by decide)
private theorem responseBuffers (signing : Bool) : (response signing).program.code.memBound ≤ 2 := by
  change (selectSlice (w := 32) 0 1).memBound ≤ 2
  decide
private def input := CallerStep.pending layout.control
private def initial (value : layout.Request × extraction.forgery.Value) := Sum.inr (α := extraction.forgery.Value) value
private def initialCode : Realizer .unit input (CallerStep.next layout.control) initial :=
  inrRealizer .unit (by decide) extraction.forgery.representation input (by decide) (by decide)
private def advance (value : extraction.forgery.Value × layout.Reply) := Sum.inl (β := layout.Request × extraction.forgery.Value) value.1
private def continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance :=
  (firstRealizer .unit (by decide) layout.state (WeightedCallerPackets.reply layout.service layout.randomBound layout.randomFits)
    (by decide) (by decide)).then
      (inlRealizer .unit (by decide) extraction.forgery.representation input (by decide) (by decide))
private def initialRaw : Stmt 32 := Assembly.code (Construction.taggedOperands 1 16 0)
private def continuationRaw : Stmt 32 := selectSlice 0 12 ;; Assembly.code (Construction.taggedOperands 0 12 4)
private theorem initial_code : initialCode.code = initialRaw := rfl
private theorem continuation_code : continuation.code = continuationRaw := rfl
private theorem initialNameFits : initialCode.savedBuffer < 2 ^ 32 := by
  change max 2 initialCode.code.memBound < 2 ^ 32
  rw [initial_code]
  have bound := (Assembly.code_names (Construction.taggedOperands (w := 32) 1 16 0) 1
    (Construction.prefix_sources 1 16 0)).2
  change initialRaw.memBound ≤ 2 at bound
  omega
private theorem continuationNameFits : continuation.savedBuffer < 2 ^ 32 := by
  change max 2 continuation.code.memBound < 2 ^ 32
  rw [continuation_code]
  have first := selectSlice_buffers (w := 32) 0 12
  have last := (Assembly.code_names (Construction.taggedOperands (w := 32) 0 12 4) 1
    (Construction.prefix_sources 0 12 4)).2
  simp only [continuationRaw, Stmt.memBound]
  omega
private def fullInput := input.prod layout.service.store.representation (by decide)
private def program (fuel : Nat) (hashes : Bool) := WeightedCallerProgram.code (base := base) (key := .atom false) (val := .atom true)
  layout oopsGenerator primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformDraw
  response responseBuffers (by decide) advance continuation continuationNameFits input initial initialCode initialNameFits (by decide) fuel
  ⟨0, trivial⟩ hashes goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide)
private def returnInitial (value : extraction.forgery.Value) := Sum.inl (β := layout.Request × extraction.forgery.Value) value
private def returnCode : Realizer .unit extraction.forgery.representation (CallerStep.next layout.control) returnInitial :=
  inlRealizer .unit (by decide) extraction.forgery.representation input (by decide) (by decide)
private theorem returnNameFits : returnCode.savedBuffer < 2 ^ 32 := by
  have bound := (Assembly.code_names (Construction.taggedOperands (w := 32) 0 12 4) 1
    (Construction.prefix_sources 0 12 4)).2
  change max 2 (Assembly.code (Construction.taggedOperands (w := 32) 0 12 4)).memBound < 2 ^ 32
  omega
private def returnedInput := extraction.forgery.representation.prod layout.service.store.representation (by decide)
private def immediate (hashes : Bool) := WeightedCallerProgram.code (base := base) (key := .atom false) (val := .atom true)
  layout oopsGenerator primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformDraw
  response responseBuffers (by decide) advance continuation continuationNameFits extraction.forgery.representation returnInitial returnCode returnNameFits (by decide) 0
  ⟨0, trivial⟩ hashes goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide)
private def forgery (target : Word 32 × Word 32) (beta : Word 32) (gamma xi : List (Word 32))
    (gammaFits : gamma.length ≤ 3) (xiFits : xi.length ≤ 4) : extraction.forgery.Value :=
  ⟨(target, beta, gamma, xi), ⟨trivial, trivial⟩, trivial, ⟨gammaFits, fun _ _ => trivial⟩, xiFits, fun _ _ => trivial⟩
private def emptyStore : layout.service.store.Value :=
  ⟨(123, [], [], []), trivial, ⟨by decide, fun _ impossible => by cases impossible⟩,
    ⟨by decide, fun _ impossible => by cases impossible⟩, by decide, fun _ impossible => by cases impossible⟩
private def fullStore : layout.service.store.Value :=
  ⟨(123, List.replicate 6 (((0 : Fin 2), 42), 99), [], []), trivial,
    ⟨by decide, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    ⟨by decide, fun _ impossible => by cases impossible⟩, by decide, fun _ impossible => by cases impossible⟩
private def hash : layout.Request := .inr (.inl ⟨(0, 42), trivial, trivial⟩)
private def sign : layout.Request := .inr (.inr ⟨(3, 42), trivial, trivial⟩)
private def admitted (fuel : Nat) (value : (layout.Request × extraction.forgery.Value) × layout.service.store.Value) : Prop :=
  WeightedOracle.Reserved layout.service layout.terms fuel value.2.val ∧
  value.2.val.2.1.length + max 1 layout.terms *
    (value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1
private theorem empty_reserved (request : layout.Request) (forged : extraction.forgery.Value) :
    admitted 1 ((request, forged), emptyStore) := by
  constructor
  · constructor
    · change (2 : Nat) ≤ 6; decide
    · change (1 : Nat) ≤ 2; decide
    · change (1 : Nat) ≤ 3; decide
  · change (6 : Nat) ≤ 6; decide
private theorem complete (fuel : Nat) (hashes : Bool) : Interactive.RefinesOn (admitted fuel) layout.port .unit fullInput scalar.representation
    (WeightedCallerProgram.denote (base := base) (key := .atom false) (val := .atom true)
      layout oopsGenerator primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
      response advance initial fuel ⟨0, trivial⟩ hashes goodExtract goodExtractBuffers (by decide) add uniformSource)
    (program fuel hashes) :=
  WeightedCallerProgram.refines (base := base) (key := .atom false) (val := .atom true) layout oopsGenerator primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformDraw
    response responseBuffers (by decide) advance continuation continuationNameFits input initial initialCode initialNameFits (by decide) fuel
    ⟨0, trivial⟩ hashes goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide)
    uniformSource uniformCorrect (fun _ => rfl) rfl uniformLaw (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (admitted fuel) (fun _ _ => trivial) (fun _ valid => valid.1) (fun _ valid => valid.2)

private def initializer :=  WeightedInitialization.code layout.service input (by decide)
private theorem initialized_admitted (value : layout.Request × extraction.forgery.Value) (config : scalar.Value) :
    admitted 1 (WeightedInitialization.initialized layout.service (value, config)) :=
  WeightedInitialization.extraction_reserved layout.service 2 1 (by decide) (by decide) (by decide) config

-- Source keys use (topic, degree), whereas stored keys use (degree, topic).
private instance : Module (Word 32) (Ty.Value base (.atom true)) :=
  inferInstanceAs (Module (Word 32) (Word 32))
private def sourceKeys : (Word 32 × Fin 2) ≃ Key := Equiv.prodComm _ _
private def sourceTerms := OOPS.LazyAGM.terms (F := Word 32) (T := Word 32) 1
private theorem terms_source (message : Word 32 × Word 32) :
    OOPSTerms.value (degree := 1) message = (sourceTerms message).map (Prod.map sourceKeys id) :=
  OOPSTerms.source 1 message
private abbrev SourceSpec := Model.LazyAGM.advSpec (Word 32 × Fin 2) (Word 32 × Word 32) (Word 32)
private abbrev SourceInput := SourceSpec.Domain × extraction.forgery.Value
private abbrev SourceState := extraction.forgery.Value ⊕ SourceInput
private def sourceStep : SourceState → extraction.forgery.Value ⊕ SourceSpec.toPFunctor.Obj SourceState
  | .inl result => .inl result
  | .inr (q, forged) => .inr ⟨q, fun _ => .inl forged⟩
private def sourceMachine : OracleMachine SourceSpec SourceInput extraction.forgery.Value :=
  PFunctor.DynSystem.DynComputation.ofStep sourceStep Sum.inr
private def sourceProgram (value : SourceInput) : OracleComp SourceSpec extraction.forgery.Value :=
  SourceSpec.query value.1 >>= fun _ => pure value.2
private theorem source_implements : sourceMachine.ImplementsWithin sourceProgram 1 := by
  intro value
  simp [sourceMachine, sourceProgram, PFunctor.DynSystem.DynComputation.run,
    PFunctor.DynSystem.DynComputation.unroll, sourceStep, bind_pure_comp]
  rfl
private def sourceInput (value : layout.Request × extraction.forgery.Value) : SourceInput :=
  (WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm value.1, value.2)
private def sourceState (value : layout.Request × extraction.forgery.Value) : sourceMachine.State :=
  .inr (sourceInput value)
private theorem advance_source (_remaining : Nat) (q : layout.Request) (c : extraction.forgery.Value) (_ : True)
    (next : SourceSpec.Range (WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm q) → sourceMachine.State)
    (view : sourceMachine.view (sourceState (q, c)) =
      .inr ⟨WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm q, next⟩)
    (represented : layout.Reply) (original : SourceSpec.Range (WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm q))
    (_ : WeightedCallerHandler.replyMatchesIn layout.service layout.randomBound sourceKeys.symm q represented original) :
    CallerMachine.Matches sourceMachine (WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm)
      sourceState (advance (c, represented)) (next original) := by
  rw [sourceMachine.next_eq_of_view_query view (show sourceMachine.view (sourceState (q, c)) =
    .inr ⟨WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm q, fun _ => .inl c⟩ from rfl)]
  exact CallerMachine.Matches.returned (machine := sourceMachine)
    (query := WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm) (state := sourceState) c (.inl c) rfl
private theorem initial_source (value : (layout.Request × extraction.forgery.Value) × layout.service.store.Value) (_ : admitted 1 value) :
    CallerMachine.Matches sourceMachine (WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm)
      sourceState (initial value.1) (sourceMachine.init (sourceInput value.1)) :=
  .pending value.1.1 value.1.2 (fun _ => .inl value.1.2) rfl

private theorem complete_source (hashes : Bool) (tape : RandomTape 32)
    (value : (layout.Request × extraction.forgery.Value) × layout.service.store.Value) (valid : admitted 1 value)
    (before : State 32) (holds : fullInput.Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe scalar.representation finished) <$>
        (program 1 hashes).execute layout.port .unit tape before =
      some <$> ((simulateQ (WeightedCallerHandler.original sourceTerms
        (fun (_ : Bool) (value : Word 32 × Word 32) => value.1)) (sourceProgram (sourceInput value.1))).run
          (WeightedOracle.decodeStore sourceKeys.symm value.2.val) >>=
        fun answer => Prod.fst <$> WeightedCallerProgram.extractionSource hashes sourceTerms
          (fun value => value.1 + value.2) (fun value => value.1 / (value.2.1 - value.2.2))
          (answer.1.val, answer.2.2)) :=
  WeightedCallerProgram.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    layout oopsGenerator primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformDraw
    response responseBuffers (by decide) advance continuation continuationNameFits input initial initialCode initialNameFits (by decide) 1
    ⟨0, trivial⟩ hashes goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide)
    uniformSource uniformCorrect rfl (fun _ => rfl) rfl uniformLaw (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (admitted 1) (fun _ _ => trivial) (fun _ accepted => accepted.1) (fun _ accepted => accepted.2)
    sourceKeys sourceTerms terms_source sourceMachine sourceState sourceInput advance_source initial_source
    sourceProgram source_implements tape value valid before holds

private def setup : WeightedSetup.Layouts layout.service (layout.Request × extraction.forgery.Value) :=
  ⟨Layout.all input, by decide⟩
private theorem routineNames {code : Stmt 32} {words : Nat} (names : NamesAccounted code 3)
    (stored : descriptionWords code ≤ words) (fits : 3 + words ≤ 65536) : NamesBound code 65536 :=
  NamesBound.mono names ((Nat.add_le_add_left stored 3).trans fits)
private def routines : WeightedFull.Routines (base := base) (key := .atom false) (val := .atom true) layout where
  generate := OOPSTerms.value (degree := 1)
  generator := oopsGenerator
  combine := fun (value : Word 32 × (Word 32 × Word 32)) => value.2.2 + value.1 * value.2.1
  update := goodUpdate
  respond := fun _ value => value.1
  response := response
  calculate := fun (value : Word 32 × (Word 32 × Word 32)) => value.1 / (value.2.1 - value.2.2)
  extract := goodExtract
  numerator := fun (value : Word 32 × Word 32) => value.1 + value.2
  sum := add
  coefficientDefault := ⟨0, trivial⟩
  slots := 65536
  reserve := by decide
  generatorNames := routineNames oopsNames oopsBound.code_le (by decide)
  updateNames := routineNames goodNames goodBound.code_le (by decide)
  responseNames _ := routineNames (Implementation.first_names _ _ _ _ 3)
    (Implementation.first_boundedBy _ _ _ _).code_le (by decide)
  extractNames := routineNames goodExtractNames goodExtractBound.code_le (by decide)
  sumNames := addNames.mono (by decide)
private def fullCaller : WeightedFull.Caller (base := base) (key := .atom false) (val := .atom true) layout setup.key.representation where
  advance := advance
  continuation := continuation
  localNameFits := continuationNameFits
  initial := fun value => initial value.val
  initialCode := initialCode.viewInput setup.key.representation Subtype.val (fun _ => rfl)
  initialNameFits := initialNameFits
private def fullInvariant : WeightedFull.Invariant (base := base) (key := .atom false) (val := .atom true) layout setup fullCaller 1 where
  domain := fun _ _ => True
  advanceValid := fun _ _ _ _ _ _ _ => trivial
  initialValid := fun _ => trivial
private def fullProgram (fuel : Nat) (hashes : Bool) :=
  WeightedFull.code (base := base) (key := .atom false) (val := .atom true) layout setup routines primitives comparison comparison_correct fullCaller uniformDraw fuel hashes
private def routineBounds : WeightedFull.Routines.Bounds (base := base) (key := .atom false) (val := .atom true) layout routines where
  generator := ⟨OOPSTerms.timeBudget oops 6, OOPSTerms.codeBudget oops 27⟩
  update := ⟨BLSAccumulate.goodTime accumulation.arithmetic 6 6, BLSAccumulate.goodCode accumulation.arithmetic 27 27⟩
  response := fun _ => ⟨8, 40⟩
  extract := ⟨BLSExtractArithmetic.goodTime accumulation.arithmetic 6 6, BLSExtractArithmetic.goodCode accumulation.arithmetic 27 27⟩
  sum := ⟨6, 27⟩
  generatorBound := oopsBound
  updateBound := goodBound
  responseBound _ := Implementation.first_boundedBy _ _ _ _
  extractBound := goodExtractBound
  sumBound := addBound
private def callerBounds : WeightedFull.Caller.Bounds (base := base) (key := .atom false) (val := .atom true) layout setup fullCaller where
  step := ⟨400, 1000⟩
  initial := ⟨400, 1000⟩
  localTime _ := by change continuationRaw.staticTime .unit ≤ 400; decide
  initialTime _ := by change initialRaw.staticTime .unit ≤ 400; decide
  localWords := by
    have raw := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 32) 0 12 4)
    change descriptionWords (Assembly.code (Construction.taggedOperands (w := 32) 0 12 4)) ≤ 26 * 17 + 14 at raw
    change descriptionWords continuationRaw ≤ 1000
    rw [continuationRaw, descriptionWords_seq, selectSlice_descriptionWords]
    omega
  initialWords := by
    have raw := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 32) 1 16 0)
    change descriptionWords initialRaw ≤ 26 * 17 + 14 at raw
    exact raw.trans (by decide)
  slots := 3
  localNames := by
    have raw := Assembly.code_names (Construction.taggedOperands (w := 32) 0 12 4) 1
      (Construction.prefix_sources 0 12 4)
    exact (selectSlice_names 0 12 3).seq (show NamesBound _ 3 from ⟨raw.1, raw.2.trans (by decide)⟩).accounted
  initialNames := by
    have raw := Assembly.code_names (Construction.taggedOperands (w := 32) 1 16 0) 1
      (Construction.prefix_sources 1 16 0)
    exact (show NamesBound _ 3 from ⟨raw.1, raw.2.trans (by decide)⟩).accounted
private theorem full_refines (hashes : Bool) : Interactive.Refines layout.port .unit setup.challenge.representation scalar.representation
    (WeightedFull.denote (base := base) (key := .atom false) (val := .atom true) layout setup routines primitives comparison comparison_correct fullCaller 1 hashes uniformSource)
    (fullProgram 1 hashes) :=
  WeightedFull.refines (base := base) (key := .atom false) (val := .atom true) layout setup routines primitives comparison comparison_correct fullCaller uniformDraw 1 hashes uniformSource
    fullInvariant (by decide) (by decide) (by decide) uniformCorrect (fun _ => rfl) rfl uniformLaw
private theorem full_within (hashes : Bool) : Interactive.Within layout.port setup.challenge scalar
    (WeightedFull.codeBudget (base := base) (key := .atom false) (val := .atom true) layout setup routines fullCaller routineBounds callerBounds hashes 125 1)
    (WeightedFull.memoryBudget (base := base) (key := .atom false) (val := .atom true) layout setup routines fullCaller routineBounds callerBounds hashes 26 125 3 1)
    (WeightedFull.timeBudget (base := base) (key := .atom false) (val := .atom true) layout setup routines fullCaller routineBounds callerBounds hashes 26 1)
    (fun value => Subtype.val <$> WeightedFull.denote (base := base) (key := .atom false) (val := .atom true) layout setup routines primitives comparison comparison_correct fullCaller 1 hashes uniformSource value) :=
  WeightedFull.within (base := base) (key := .atom false) (val := .atom true) layout setup routines fullCaller routineBounds callerBounds primitives comparison comparison_correct
    uniformDraw 1 hashes uniformSource uniformCorrect
    (UniformSampling.time_bound (w := 32) 4294967295 (by decide) (by decide) 4294967295)
    (UniformSampling.code_words (w := 32) 4294967295 (by decide) (by decide) 4294967295)
    (UniformSampling.names (w := 32) 4294967295 (by decide) (by decide) 4294967295)
    fullInvariant (by decide) (by decide) (by decide) (fun _ => rfl) rfl uniformLaw
    (UniformSampling.descriptionFits (w := 32) 4294967295 (by decide) (by decide) 4294967295) (by decide) (by decide)
private def fullSourceMachine : OracleMachine SourceSpec (layout.Request × extraction.forgery.Value) extraction.forgery.Value :=
  PFunctor.DynSystem.DynComputation.ofStep sourceStep (fun value => .inr (sourceInput value))
private def fullCorrespondence : WeightedFull.Correspondence (base := base) (key := .atom false) (val := .atom true) layout setup fullCaller 1 fullInvariant sourceKeys where
  source := fun value => sourceProgram (sourceInput value)
  machine := fullSourceMachine
  implements := fun value => source_implements (sourceInput value)
  stateView := sourceState
  advanceMatches := by
    intro remaining q c valid next view represented original matched
    rw [fullSourceMachine.next_eq_of_view_query view (show fullSourceMachine.view (sourceState (q, c)) =
      .inr ⟨WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm q, fun _ => .inl c⟩ from rfl)]
    exact CallerMachine.Matches.returned (machine := fullSourceMachine)
      (query := WeightedCallerHandler.queryIn layout.service layout.randomBound sourceKeys.symm) (state := sourceState) c (.inl c) rfl
  initialMatches value := .pending value.val.1 value.val.2 (fun _ => .inl value.val.2) rfl
private theorem initialized_source (hashes : Bool) (value : setup.challenge.Value) :
    Subtype.val <$> WeightedFull.denote (base := base) (key := .atom false) (val := .atom true) layout setup routines primitives comparison comparison_correct fullCaller 1 hashes uniformSource value =
      ((simulateQ (WeightedCallerHandler.original sourceTerms (fun (_ : Bool) (value : Word 32 × Word 32) => value.1))
        (sourceProgram (sourceInput value.val.2.2))).run (value.val.1, [], [], []) >>=
          fun answer => Prod.fst <$> WeightedCallerProgram.extractionSource hashes sourceTerms
            (fun value => value.1 + value.2) (fun value => value.1 / (value.2.1 - value.2.2)) (answer.1.val, answer.2.2)) :=
  WeightedFull.denote_source (base := base) (key := .atom false) (val := .atom true) layout setup fullCaller 1 fullInvariant sourceKeys routines primitives comparison comparison_correct hashes
    uniformSource rfl (fun _ => rfl) rfl uniformLaw (by decide) (by decide) (by decide)
    sourceTerms terms_source fullCorrespondence value

-- The sampled bad program uses two independent scalar draws per cached key.
private abbrev pairTy : Ty Bool := .pair (.atom true) (.atom true)
private instance : SampleableType (Ty.Value base pairTy) := inferInstanceAs (SampleableType (Word 32 × Word 32))
private instance : AddCommMonoid (Ty.Value base pairTy) := inferInstanceAs (AddCommMonoid (Word 32 × Word 32))
private instance : SMul (Word 32) (Ty.Value base pairTy) := inferInstanceAs (SMul (Word 32) (Word 32 × Word 32))
private def groupLayout : BLSResponse.Layouts 32 (Word 32) (Word 32) := ⟨scalar, scalar, by decide, by decide⟩
private def scale : Implementation .unit groupLayout.scaleArgs scalar (fun value => value.1 • value.2) := mul
private def badSigning : WeightedExtraction.Layouts 32 Key (Word 32 × Word 32) (Word 32) (Word 32) (Word 32 × Word 32) :=
  ⟨⟨⟨accumulation.bad, oops.input, by decide⟩, scalar, by decide⟩,
    3, 4, 2, by decide, by decide, by decide, by decide, by decide⟩
private def badExtraction : WeightedExtractor.Layouts 32 Key (Word 32 × Word 32) (Word 32) (Word 32) (Word 32 × Word 32) :=
  ⟨badSigning, 2, 3, by decide, by decide, by decide⟩
private def badLayout : WeightedCallerExtraction.Layouts 32 Key (Word 32 × Word 32) (Word 32) (Word 32) (Word 32 × Word 32)
    (Word 32 × (Word 32 × Word 32)) extraction.forgery.Value where
  extraction := badExtraction
  config := groupLayout.config
  zero := ⟨(0, 0), trivial, trivial⟩
  default := ⟨(99, 98), trivial, trivial⟩
  hashPositive := by decide
  signPositive := by decide
  serviceFits := by decide
  randomBound := 4294967295
  randomFits := by decide
  state := extraction.forgery.representation
  callerFits := by decide
private def badSetup : WeightedSetup.Layouts badLayout.service (Word 32) := ⟨scalar, by decide⟩
private def preparation : WeightedBadSetup.Layouts 32 (Word 32) (Word 32) (Word 32) :=
  ⟨scalar, groupLayout.points, scalar, by decide, by decide⟩
private def resampling : WeightedFull.Resampling (base := base) (key := .atom false) (val := pairTy) badLayout badSetup where
  preparation := preparation
  compatible := rfl
  scale := scale
  slots := 3
  reserve := by decide
  names := mulNames
  budget := ⟨6, 27⟩
  bounded := mulBound
private def pairDraw := PairSampling.code scalar scalar (by decide) (by decide) uniformPort uniformDraw uniformDraw
private def pairSource := PairSampling.denote scalar scalar (by decide) uniformSource uniformSource
private theorem pairCorrect : Interactive.Refines badLayout.port .unit badLayout.service.evaluation.cache.lookup.unit.representation
    badLayout.service.evaluation.cache.value.representation (fun _ => pairSource) pairDraw :=
  PairSampling.refines (hw := by decide) (fits := by decide) uniformCorrect uniformCorrect
private theorem pairLaw : Subtype.val <$> pairSource = ($ᵗ (Ty.Value base pairTy) : ProbComp _) :=
  PairSampling.uniform scalar scalar (by decide) uniformSource uniformSource uniformLaw uniformLaw
private def badResponse := BLSResponse.bad groupLayout scale add mulNames.buffers (by decide) addNames.buffers
private theorem badUpdateBound : badUpdate.BoundedBy
    (BLSAccumulate.badTime accumulation.arithmetic 6 6) (BLSAccumulate.badCode accumulation.arithmetic 27 27) :=
  BLSAccumulate.bad_bounded accumulation.arithmetic mul add mulBound addBound mulNames.buffers (by decide) addNames.buffers
private theorem badUpdateNames : NamesAccounted badUpdate.program.code 3 :=
  BLSAccumulate.bad_names accumulation.arithmetic 3 mul add mulNames.accounted addNames.accounted mulNames.buffers (by decide) addNames.buffers
private theorem badExtractorNames : NamesAccounted badExtract.program.code 3 :=
  BLSExtractArithmetic.bad_names accumulation.arithmetic 3 sub subNames.accounted subNames.buffers (by decide)
    negate negNames.accounted negNames.buffers divide divNames.accounted
private def unusedSum : Implementation .unit badExtraction.numeratorInput scalar (fun value => value.1) :=
  Implementation.first (by decide) scalar accumulation.bad.cache.value (by decide) (by decide)
private def badRoutines : WeightedFull.Routines (base := base) (key := .atom false) (val := pairTy) badLayout where
  generate := OOPSTerms.value (degree := 1)
  generator := oopsGenerator
  combine := fun (value : Word 32 × ((Word 32 × Word 32) × (Word 32 × Word 32))) =>
    (value.2.2.1 + value.1 * value.2.1.1, value.2.2.2 + value.1 * value.2.1.2)
  update := badUpdate
  respond := fun signing (value : (Word 32 × Word 32) × (Word 32 × (Word 32 × Word 32))) =>
    if signing then value.2.1 • (value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
    else value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1
  response := badResponse
  calculate := fun (value : Word 32 × ((Word 32 × Word 32) × (Word 32 × Word 32))) =>
    -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1)
  extract := badExtract
  numerator := fun value => value.1
  sum := unusedSum
  coefficientDefault := ⟨0, trivial⟩
  slots := 65536
  reserve := by decide
  generatorNames := routineNames oopsNames oopsBound.code_le (by decide)
  updateNames := routineNames badUpdateNames badUpdateBound.code_le (by decide)
  responseNames signing := routineNames
    (BLSResponse.bad_names groupLayout 3 scale add mulNames.accounted addNames.accounted mulNames.buffers (by decide) addNames.buffers signing)
    (BLSResponse.bad_bounded groupLayout scale add mulBound addBound mulNames.buffers (by decide) addNames.buffers signing).code_le
    (by cases signing <;> decide)
  extractNames := routineNames badExtractorNames badExtractBound.code_le (by decide)
  sumNames := routineNames (Implementation.first_names _ _ _ _ 3) (Implementation.first_boundedBy _ _ _ _).code_le (by decide)
private def badHead : badLayout.forgery.Value ⊕ (badLayout.Request × extraction.forgery.Value) :=
  .inr (.inr (.inr ⟨(2, 42), trivial, trivial⟩), forgery (3, 42) 0 [] [1] (by decide) (by decide))
private def badInitial := Implementation.constant scalar (Layout.all (CallerStep.next badLayout.control)) ⟨badHead, trivial⟩ (by decide)
private def badCaller : WeightedFull.Caller (base := base) (key := .atom false) (val := pairTy) badLayout badSetup.key.representation where
  advance := advance
  continuation := continuation
  localNameFits := continuationNameFits
  initial := fun _ => badHead
  initialCode := badInitial.program.viewOutput (CallerStep.next badLayout.control) (fun _ => badHead) (fun _ => rfl)
  initialNameFits := by
    have buffers := Implementation.constant_buffers scalar (Layout.all (CallerStep.next badLayout.control)) ⟨badHead, trivial⟩ (by decide)
    change max 2 badInitial.program.code.memBound < 2 ^ 32
    dsimp only [badInitial]
    omega
private def badInvariant : WeightedFull.Invariant (base := base) (key := .atom false) (val := pairTy) badLayout badSetup badCaller 1 where
  domain := fun _ _ => True
  advanceValid := fun _ _ _ _ _ _ _ => trivial
  initialValid := fun _ => trivial
private def badRoutineBounds : WeightedFull.Routines.Bounds (base := base) (key := .atom false) (val := pairTy) badLayout badRoutines where
  generator := ⟨OOPSTerms.timeBudget oops 6, OOPSTerms.codeBudget oops 27⟩
  update := ⟨BLSAccumulate.badTime accumulation.arithmetic 6 6, BLSAccumulate.badCode accumulation.arithmetic 27 27⟩
  response := fun signing => ⟨BLSResponse.badTime groupLayout signing 6 6, BLSResponse.badWords groupLayout signing 27 27⟩
  extract := ⟨BLSExtractArithmetic.badTime accumulation.arithmetic 6 118 6, BLSExtractArithmetic.badCode accumulation.arithmetic 27 631 27⟩
  sum := ⟨8, 40⟩
  generatorBound := oopsBound
  updateBound := badUpdateBound
  responseBound := BLSResponse.bad_bounded groupLayout scale add mulBound addBound mulNames.buffers (by decide) addNames.buffers
  extractBound := badExtractBound
  sumBound := Implementation.first_boundedBy _ _ _ _
private def badCallerBounds : WeightedFull.Caller.Bounds (base := base) (key := .atom false) (val := pairTy) badLayout badSetup badCaller where
  step := ⟨400, 1000⟩
  initial := ⟨400, 1000⟩
  localTime := callerBounds.localTime
  initialTime value := ((Implementation.constant_bounded scalar (Layout.all (CallerStep.next badLayout.control))
    ⟨badHead, trivial⟩ (by decide)).time_le value).trans (by decide)
  localWords := callerBounds.localWords
  initialWords := (Implementation.constant_bounded scalar (Layout.all (CallerStep.next badLayout.control))
    ⟨badHead, trivial⟩ (by decide)).code_le.trans (by decide)
  slots := 3
  localNames := callerBounds.localNames
  initialNames := Implementation.constant_names scalar
    (Layout.all (CallerStep.next badLayout.control)) ⟨badHead, trivial⟩ (by decide) 3
private def badProgram (fuel : Nat) := WeightedFull.badCode (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines
  primitives comparison comparison_correct badCaller pairDraw uniformDraw fuel
private theorem sampled_bad_refines : Interactive.Refines badLayout.port .unit preparation.challenge.representation scalar.representation
    (WeightedFull.badSource (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines primitives comparison comparison_correct badCaller 1 pairSource uniformSource)
    (badProgram 1) :=
  WeightedFull.bad_refines (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines primitives comparison comparison_correct badCaller
    pairDraw uniformDraw 1 pairSource uniformSource uniformCorrect pairCorrect (fun _ => rfl) rfl pairLaw badInvariant
    (by decide) (by decide) (by decide)
private theorem sampled_bad_within : Interactive.Within badLayout.port preparation.challenge scalar
    (WeightedFull.badCodeBudget (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines badCaller badRoutineBounds badCallerBounds
      (PairSampling.codeBudget scalar scalar 125 125) 125 1)
    (WeightedFull.badMemoryBudget (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines badCaller badRoutineBounds badCallerBounds
      (PairSampling.timeBudget scalar scalar 26 26) 26 (PairSampling.codeBudget scalar scalar 125 125) 125 (PairSampling.slots 3 3) 3 1)
    (WeightedFull.badTimeBudget (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines badCaller badRoutineBounds badCallerBounds
      (PairSampling.timeBudget scalar scalar 26 26) 26 1)
    (fun value => Subtype.val <$> WeightedFull.badSource (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines primitives comparison comparison_correct badCaller 1 pairSource uniformSource value) := by
  have drawTime := UniformSampling.time_bound (w := 32) 4294967295 (by decide) (by decide) 4294967295
  have drawWords := UniformSampling.code_words (w := 32) 4294967295 (by decide) (by decide) 4294967295
  have drawNames := UniformSampling.names (w := 32) 4294967295 (by decide) (by decide) 4294967295
  have drawFits := UniformSampling.descriptionFits (w := 32) 4294967295 (by decide) (by decide) 4294967295
  exact WeightedFull.bad_within (base := base) (key := .atom false) (val := pairTy) badLayout badSetup resampling badRoutines badCaller badRoutineBounds badCallerBounds
    primitives comparison comparison_correct pairDraw uniformDraw 1 pairSource uniformSource pairCorrect uniformCorrect
    (PairSampling.time_bound (hw := by decide) (fits := by decide) uniformCorrect uniformCorrect drawTime drawTime) drawTime
    (PairSampling.code_bound scalar scalar (by decide) (by decide) uniformPort uniformDraw uniformDraw drawWords drawWords) drawWords
    (PairSampling.names scalar scalar (by decide) (by decide) uniformPort uniformDraw uniformDraw drawNames drawNames) drawNames
    badInvariant (by decide) (by decide) (by decide) (fun _ => rfl) rfl pairLaw
    (PairSampling.descriptionFits scalar scalar (by decide) (by decide) uniformPort uniformDraw uniformDraw drawFits drawFits drawNames (by decide))
    drawFits (by decide) (by decide) (by decide)

open Lean in
run_cmd do
  -- The hash queried by the caller is reused by hash correction and target evaluation.
  -- Signing evaluates two terms; repeated target terms consume no additional draws.
  let tests : List (Nat × Bool × layout.Request × extraction.forgery.Value × List (Word 32) × Word 32) := [
    (1, true, hash, forgery (3, 42) 28 [3] [] (by decide) (by decide), [2, 5], 2),
    (1, false, hash, forgery (3, 42) 34 [999] [] (by decide) (by decide), [2, 5], 2),
    (1, true, sign, forgery (3, 42) 99 [] [1] (by decide) (by decide), [2, 5], 0),
    (1, true, sign, forgery (1, 43) 4294967289 [] [1] (by decide) (by decide), [2, 5, 3, 7], 1),
    (0, true, hash, forgery (3, 42) 28 [3] [] (by decide) (by decide), [], 0),
    (0, false, sign, forgery (3, 42) 99 [] [1] (by decide) (by decide), [], 0)]
  for (fuel, hashes, request, forged, draws, expected) in tests do
    let value := ((request, forged), emptyStore)
    let replies := draws.flatMap (fun sample => [4294967295, sample]) ++ [88]
    match executeUniform fullInput scalar (program fuel hashes) value replies with
    | none => throwError "weighted caller plus extraction failed"
    | some (answer, framed, capacity, register, tape, scratch, trace, remaining, _) =>
      let expectedTrace := draws.flatMap (fun sample => [WordIO.Event.output 4294967295, .invoke, .input 4294967295, .input sample])
      unless answer == expected && framed == #[77] && capacity == 4 && register == 91 && tape == 9 &&
          scratch && trace == expectedTrace && remaining == [88] do
        throwError "weighted caller changed result/cache reuse/frame/cutoff: {answer.toNat}, expected {expected.toNat}"
  for (fuel, hashes, request, forged, draws, expected) in tests do
    let key := (request, forged)
    let challenge : setup.challenge.Value := ⟨(123, (key, key)), trivial, trivial, trivial⟩
    let replies := draws.flatMap (fun sample => [4294967295, sample]) ++ [88]
    match executeUniform setup.challenge.representation scalar (fullProgram fuel hashes) challenge replies with
    | none => throwError "initialized weighted program failed"
    | some (answer, framed, capacity, register, tape, scratch, trace, remaining, elapsed) =>
      let expectedTrace := draws.flatMap (fun sample => [WordIO.Event.output 4294967295, .invoke, .input 4294967295, .input sample])
      unless answer == expected && framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
          trace == expectedTrace && remaining == [88] &&
          elapsed ≤ WeightedFull.timeBudget (base := base) (key := .atom false) (val := .atom true) layout setup routines fullCaller routineBounds callerBounds hashes 26 fuel do
        throwError "initialized weighted program changed source result, lazy draws, frame, scratch or elapsed bound"
  for hashes in [true, false] do
    let forged := forgery (3, 42) 34 [] [] (by decide) (by decide)
    match executeUniform returnedInput scalar (immediate hashes) (forged, emptyStore)
        [4294967295, 2, 4294967295, 5, 88] with
    | none => throwError "immediate return failed to enter extraction"
    | some (answer, framed, capacity, register, tape, scratch, trace, remaining, _) =>
      unless answer == 2 && framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
          trace == [WordIO.Event.output 4294967295, .invoke, .input 4294967295, .input 2,
            .output 4294967295, .invoke, .input 4294967295, .input 5] && remaining == [88] do
        throwError "immediate return changed extraction or framing"
    -- A cutoff never enters extraction, even when the existing cache is full.
    match executeUniform fullInput scalar (program 0 hashes) ((sign, forged), fullStore) [88] with
    | none => throwError "full-store cutoff failed"
    | some (answer, _, _, _, _, scratch, trace, remaining, _) =>
      unless answer == 0 && scratch && trace == [] && remaining == [88] do
        throwError "cutoff sampled from the full cache"
  for request in [hash, sign] do
    let forged := forgery (3, 42) 28 [3] [] (by decide) (by decide)
    let callerInput := (request, forged)
    match executeUniform (WeightedInitialization.input layout.service input (by decide)) (Layout.all fullInput)
        (.compute initializer.code) (callerInput, ⟨123, trivial⟩) [88] with
    | none => throwError "weighted store initialization failed"
    | some (answer, framed, capacity, register, tape, scratch, trace, remaining, elapsed) =>
      unless fullInput.encoding.encode answer == fullInput.encoding.encode (callerInput, emptyStore) &&
          framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch && trace == [] &&
          remaining == [88] && elapsed ≤ 8 * fullInput.encoding.words do
        throwError "weighted initializer changed runtime input, configuration, padding, frame, or time"
  for (g, x, generator, pk, sampled) in ([(3, 5, 7, 11, 2), (13, 17, 19, 23, 3), (3, 5, 7, 11, 0)] :
      List (Word 32 × Word 32 × Word 32 × Word 32 × Word 32)) do
    let challenge : preparation.challenge.Value := ⟨((g, x), (generator, pk)), ⟨trivial, trivial⟩, trivial, trivial⟩
    match executeUniform preparation.challenge.representation preparation.output
        (WeightedBadSetup.code preparation scale mulNames.buffers (by decide) uniformPort uniformDraw)
        challenge [4294967295, sampled, 88] with
    | none => throwError "sampled weighted key preparation failed"
    | some (answer, framed, capacity, register, tape, scratch, trace, remaining, elapsed) =>
      unless answer == ((sampled, (g, x)), (generator, sampled * generator)) && framed == #[77] && capacity == 4 &&
          register == 91 && tape == 9 && scratch && remaining == [88] &&
          trace == [WordIO.Event.output 4294967295, .invoke, .input 4294967295, .input sampled] &&
          elapsed ≤ WeightedBadSetup.timeBudget preparation 26 6 do
        throwError "sampled preparation changed runtime points/key, uniform draw, frame, scratch or time"
    for fuel in [0, 1] do
      let draws := if fuel == 0 then [sampled] else [sampled, 2, 5, 3, 4294967293]
      let replies := draws.flatMap (fun sample => [4294967295, sample]) ++ [88]
      match executeUniform preparation.challenge.representation scalar (badProgram fuel) challenge replies with
      | none => throwError "complete sampled weighted bad program failed"
      | some (answer, framed, capacity, register, tape, scratch, trace, remaining, elapsed) =>
        let expectedTrace := draws.flatMap (fun sample => [WordIO.Event.output 4294967295, .invoke, .input 4294967295, .input sample])
        unless answer == (if fuel == 0 then 0 else 1) && framed == #[77] && capacity == 4 && register == 91 &&
            tape == 9 && scratch && trace == expectedTrace && remaining == [88] &&
            elapsed ≤ WeightedFull.badTimeBudget (base := base) (key := .atom false) (val := pairTy)
              badLayout badSetup resampling badRoutines badCaller badRoutineBounds badCallerBounds
              (PairSampling.timeBudget scalar scalar 26 26) 26 fuel do
          throwError "sampled bad program changed paired cache reuse, cutoff, scalar result, trace, frame, scratch or time"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedCallerFinish.refines, ``WeightedCallerFinish.time_bound, ``WeightedCallerFinish.resources,
      ``WeightedCallerFinish.extraction_ready, ``WeightedCallerExtraction.called_postcondition, ``WeightedCallerExtraction.called_ready,
      ``WeightedCallerExtraction.refines, ``WeightedCallerExtraction.time, ``WeightedCallerExtraction.words,
      ``WeightedCallerExtraction.names, ``WeightedCallerExtraction.descriptionFits, ``WeightedCallerExtraction.resources,
      ``WeightedCallerProgram.refines, ``WeightedCallerProgram.time, ``WeightedCallerProgram.words,
      ``WeightedCallerProgram.names, ``WeightedCallerProgram.descriptionFits, ``WeightedCallerProgram.resources, ``empty_reserved, ``complete,
      ``WeightedCallerHandler.synchronizes_equiv, ``WeightedCallerHandler.original_run,
      ``WeightedCallerExtraction.finish_source, ``WeightedCallerExtraction.called_source,
      ``WeightedCallerExtraction.denote_source, ``WeightedCallerExtraction.observe_source,
      ``WeightedCallerExtraction.finish_equiv, ``WeightedCallerExtraction.called_equiv,
      ``WeightedCallerExtraction.denote_equiv, ``WeightedCallerExtraction.observe_equiv,
      ``WeightedCallerProgram.extraction_source, ``WeightedCallerProgram.denote_source, ``WeightedCallerProgram.observe_source,
      ``WeightedCallerProgram.extraction_equiv, ``WeightedCallerProgram.denote_equiv, ``WeightedCallerProgram.observe_equiv,
      ``WeightedCallerProgram.good_extraction_original, ``WeightedCallerProgram.bad_extraction_original,
      ``WeightedCallerProgram.good_original_finish, ``WeightedCallerProgram.bad_original_finish,
      ``source_implements, ``advance_source, ``initial_source, ``complete_source,
      ``WeightedInitialization.code, ``WeightedInitialization.time, ``WeightedInitialization.words,
      ``WeightedInitialization.names, ``WeightedInitialization.buffers, ``WeightedInitialization.reserved,
      ``WeightedInitialization.extraction_reserved, ``WeightedInitialization.implementation_bounded, ``initialized_admitted,
      ``WeightedSetup.implementation, ``WeightedSetup.bounded, ``WeightedSetup.names, ``WeightedSetup.buffers,
      ``WeightedFull.refines, ``WeightedFull.denote_source, ``WeightedFull.observe_source,
      ``WeightedFull.time, ``WeightedFull.words, ``WeightedFull.names, ``WeightedFull.descriptionFits, ``WeightedFull.within,
      ``WeightedFull.good_source, ``WeightedFull.good_dlogWithin, ``full_refines, ``full_within, ``initialized_source,
      ``WeightedBadSetup.refines, ``WeightedBadSetup.denote_uniform, ``WeightedBadSetup.bounded,
      ``WeightedBadSetup.time, ``WeightedBadSetup.words, ``WeightedBadSetup.names, ``WeightedBadSetup.descriptionFits,
      ``WeightedFull.bad_refines, ``WeightedFull.bad_time, ``WeightedFull.bad_words, ``WeightedFull.bad_names,
      ``WeightedFull.bad_descriptionFits, ``WeightedFull.bad_within, ``WeightedFull.bad_fixed_source,
      ``WeightedFull.bad_source, ``WeightedFull.bad_dlogWithin, ``sampled_bad_refines, ``sampled_bad_within] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"
end SignaturesTest.CaliperWeightedCaller
