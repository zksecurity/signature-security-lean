import Signatures.Runtime.Caliper.SchnorrAGMSamplingMemory
import Signatures.Runtime.Caliper.SchnorrAGMSamplingSource
import Signatures.Runtime.Caliper.EncodedConstant
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMSigning
open CaliperBackend.SchnorrAGM.Signing

-- Modular words test the executed routing and resource contracts. The generic
-- field/group theorem separately identifies the original signing arithmetic.
private instance : SMul (Word 16) (Word 16) := ⟨fun scalar point => scalar * point⟩
private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 2 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : CaliperBackend.SchnorrAGM.Signing.Histories.Layouts 16 Nat (Word 16) (Word 16) 1 2 where
  signing := { scheme := scheme, storageFits := by decide }
  counterFits := by decide

private def scale : Implementation .unit layout.signing.arithmetic.scaleArgs scheme.point (fun input => input.1 • input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput layout.signing.arithmetic.scaleArgs.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput scheme.point.representation
      (fun input => ⟨input.val.1 * input.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit layout.signing.arithmetic.points scheme.point (fun input => input.1 - input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput layout.signing.arithmetic.points.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput scheme.point.representation
      (fun input => ⟨input.val.1 - input.val.2, trivial⟩) (fun _ => rfl)
private def zero : Implementation .unit scheme.scalar scheme.scalar (fun _ => 0) :=
  Implementation.constant scheme.scalar scheme.scalar ⟨0, trivial⟩ scheme.wordFits
private def negArgs : Implementation .unit scheme.scalar scheme.affine (fun input => (0, input)) :=
  zero.pair (Implementation.identity scheme.scalar (by decide)) (by decide) scheme.wordFits
    (by decide) (by decide) (by decide) (by decide) scheme.affine.representation.fits
private def negate : Implementation .unit scheme.scalar scheme.scalar Neg.neg :=
  (negArgs.then sub).castFunction (by funext input; exact BitVec.zero_sub input)
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem negateBound : negate.BoundedBy 118 631 := by
  have zeroBound := Implementation.constant_bounded scheme.scalar scheme.scalar ⟨0, trivial⟩ scheme.wordFits
  have paired : negArgs.BoundedBy 112 603 := by
    apply (Implementation.pair_boundedBy zero (Implementation.identity scheme.scalar (by decide))
      scheme.wordFits (by decide) (by decide) (by decide) (by decide) scheme.affine.representation.fits
      zeroBound (Implementation.identity_boundedBy scheme.scalar (by decide))).mono <;> decide
  apply ((paired.then subBound).castFunction _).mono <;> decide
private theorem scaleNames : NamesBound scale.program.code 3 := ⟨by decide, by decide⟩
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private theorem negateNames : NamesBound negate.program.code 3 := ⟨by decide, by decide⟩

private def sampleSpec : OracleSpec Unit := fun _ => scheme.scalar.Value
private def replyView : (Σ _ : (PairSampling.input 16).Value, scheme.scalar.Value) ≃ scheme.scalar.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 16 sampleSpec where
  Request := (PairSampling.input 16).Value
  source _ := ()
  request := (PairSampling.input 16).representation
  reply := scheme.scalar.representation.transport replyView
private def sampleSource : OracleComp sampleSpec scheme.scalar.Value := queryBind () Pure.pure
private def sampler : Interactive.Code 16 := .query
private theorem sampleCorrect : Interactive.Refines port .unit (PairSampling.input 16).representation
    scheme.scalar.representation (fun _ => sampleSource) sampler := by
  have projected := (Interactive.Refines.query port .unit).viewOutput scheme.scalar.representation
    (fun packet => packet.2) (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem sampleTime : Interactive.TimeBound port .unit (PairSampling.input 16).representation sampler 4 :=
  Interactive.TimeBound.query
private theorem sampleWords : (sampler.lower port).descriptionWords ≤ 20 := by decide
private theorem sampleNames : WordIO.NamesBound (sampler.lower port) 3 := ⟨by decide, by decide⟩
private theorem sampleFits : (sampler.lower port).DescriptionFits :=
  WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)

private def deterministic := Sampled.implementation layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide)
private def program := Sampling.code layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
private def source := Sampling.denote layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) sampleSource
private def timeBudget := Sampling.timeBudget layout 6 6 118 4
private def codeBudget := Sampling.codeBudget layout 27 27 631 20
private def nameBudget := Sampling.nameBudget 3 3
private theorem deterministicBound : deterministic.BoundedBy (Sampled.timeBudget layout 6 6 118) (Sampled.codeBudget layout 27 27 631) :=
  Sampled.bounded layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) scaleBound subBound negateBound
private theorem deterministicNamed : NamesAccounted deterministic.program.code 5 :=
  Sampled.names (named := 3) layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide)
    scaleNames.accounted subNames.accounted negateNames.accounted
private theorem deterministicBuffers : deterministic.program.code.memBound ≤ 9 :=
  Sampled.buffers layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide)
private theorem refined : Interactive.Refines port .unit (Sampling.input layout).representation
    (Programming.output layout).representation source program :=
  Sampling.refines layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampleCorrect
private theorem timed : Interactive.TimeBound port .unit (Sampling.input layout).representation program timeBudget :=
  Sampling.time_bound layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port
    sampleCorrect scaleBound subBound negateBound sampleTime
private theorem stored : (program.lower port).descriptionWords ≤ codeBudget :=
  Sampling.code_bound layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
    scaleBound subBound negateBound sampleWords
private theorem named : WordIO.NamesAccounted (program.lower port) nameBudget :=
  Sampling.names (primitiveNames := 3) (sampleSlots := 3) layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
    scaleNames.accounted subNames.accounted negateNames.accounted sampleNames
private theorem accepted : (program.lower port).DescriptionFits :=
  Sampling.descriptionFits layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
    sampleFits sampleNames (by decide)

private theorem valid_iff (g pk : Word 16) (message : Nat)
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    (Sampling.input layout).valid (g, pk, message, entries, basis, signed, malformed, bad) ↔
      (message < 256 ∧ (entries.length ≤ 4 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 4 ∧ signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧
        entries.length ≤ 3 ∧ basis.length < 4 ∧ signed.length < 2 := by
  change (True ∧ True ∧ message < 256 ∧
    (entries.length ≤ 4 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 4 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _ ↔ _
  simp only [true_and, and_true, implies_true, and_assoc]
  rfl

private def fresh : (Sampling.input layout).Value :=
  ⟨(3, 5, 7, [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1)], [3], false, false), by rw [valid_iff]; decide⟩
private def collision : (Sampling.input layout).Value :=
  ⟨(3, 5, 7, [((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12))],
    [(5, 7), (1, 0), (0, 1)], [7], true, true), by rw [valid_iff]; decide⟩
private def finalSlot : (Sampling.input layout).Value :=
  ⟨(5, 3, 255, [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14))],
    [(1, 0), (0, 1), (5, 7)], [9], false, true), by rw [valid_iff]; decide⟩
private def empty : (Sampling.input layout).Value :=
  ⟨(5, 3, 0, [], [], [], true, false), by rw [valid_iff]; decide⟩

example : ¬ (Sampling.input layout).valid (1, 1, 256, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ (Sampling.input layout).valid (1, 1, 0, [], List.replicate 4 (0, 0), [], false, false) := by rw [valid_iff]; decide
example : ¬ (Sampling.input layout).valid (1, 1, 0, [], [], [1, 2], false, false) := by rw [valid_iff]; decide
example : ¬ (Sampling.input layout).valid (1, 1, 0, List.replicate 4 ((0, 0), (0, false, 0, 0)), [], [], false, false) := by rw [valid_iff]; decide
example : ¬ (Sampling.input layout).valid (1, 1, 0, [], [], [256], false, false) := by rw [valid_iff]; decide
example : ¬ (Sampling.input layout).valid (1, 1, 0, [((256, 0), (0, false, 0, 0))], [], [], false, false) := by rw [valid_iff]; decide

private theorem sampled_valid_iff (c z g pk : Word 16) (message : Nat)
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    (Sampled.input layout).valid ((c, z), g, pk, message, entries, basis, signed, malformed, bad) ↔
      (message < 256 ∧ (entries.length ≤ 4 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 4 ∧ signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧
        (basis.length < 4 ∧ signed.length < 2) ∧
        scheme.cache.admissible ((message, z • g - c • pk), (c, false, 0, 0), entries, ()) := by
  change ((True ∧ True) ∧ True ∧ True ∧ message < 256 ∧
    (entries.length ≤ 4 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 4 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _ ↔ _
  dsimp only [Sampled.admissible, Histories.Layouts.room, Sampled.cacheRoom, Arithmetic.value]
  simp only [true_and, and_true, implies_true, and_assoc]
  rfl

-- The deterministic stage admits full-table hits even though the sampling
-- entry point uses the stronger reachable-state reservation for arbitrary draws.
private def fullHit : (Sampled.input layout).Value :=
  ⟨((2, 11), 3, 5, 7,
    [((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14)), ((8, 9), (3, true, 15, 16))],
    [(5, 7), (1, 0), (0, 1)], [7], true, true), by rw [sampled_valid_iff]; decide⟩
private def zeroScheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 0 where
  scalar := scheme.scalar
  point := scheme.point
  message := scheme.message
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def zeroLayout : Histories.Layouts 16 Nat (Word 16) (Word 16) 1 0 where
  signing := { scheme := zeroScheme, storageFits := by decide }
  counterFits := by decide
private theorem zeroAdmission (args : Sampling.RequestState Nat (Word 16) (Word 16)) :
    ¬ (Sampling.input zeroLayout).valid args := fun valid => Nat.not_lt_zero _ valid.2.2.2

private theorem memory (tape : RandomTape 16) (args : (Sampling.input layout).Value) (before : State 16)
    (holds : (Sampling.input layout).representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute port .unit tape before)) :
    finished.time ≤ timeBudget ∧ ∃ answer ∈ support (source args),
      (Programming.output layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (program.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((program.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (program.lower port).memBound) ≤
            5 * codeBudget + 4 * nameBudget + registers + 3 * buffers + before.liveMem buffers + timeBudget := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    Sampling.resources layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port
      sampleCorrect scaleBound subBound negateBound sampleTime sampleWords scaleNames.accounted subNames.accounted negateNames.accounted
      sampleNames tape args before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def execute (args : (Sampling.input layout).Value) (replies : List (Word 16)) := do
  let initial := (Sampling.input layout).representation.initial args
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ timeBudget))

private def executeSampled (args : (Sampling.input layout).Value) (c z : Word 16) :=
  let sampled := Sampling.sampleValue layout (⟨(c, z), trivial, trivial⟩, args)
  (Caliper.run .unit RandomTape.zero 1000000 deterministic.program.code ((Sampled.input layout).representation.initial sampled)).map
    (fun result => (result.1.bufs 0, (List.range 30).all (fun i => result.1.caps (i + 1) == 0),
      decide (result.2.1 ≤ Sampled.timeBudget layout 6 6 118)))

open Lean in
run_cmd do
  let freshBytes : Array (Word 16) := #[23, 11, 2, 7, 23, 2, 0, 0, 0, 5, 6, 1, 1, 13, 14] ++ Array.replicate 12 0 ++
    #[3, 1, 0, 0, 1, 11, 65534, 0, 0, 2, 3, 7, 0, 0]
  let hitBytes : Array (Word 16) := #[23, 11, 2, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12] ++ Array.replicate 12 0 ++
    #[4, 5, 7, 1, 0, 0, 1, 11, 65534, 2, 7, 7, 1, 1]
  let finalBytes : Array (Word 16) := #[13, 2, 4, 255, 13, 65535, 0, 0, 0, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12,
    5, 6, 1, 0, 13, 14, 4, 1, 0, 0, 1, 5, 7, 2, 1, 2, 9, 255, 0, 1]
  let emptyBytes : Array (Word 16) := #[0, 0, 1] ++ Array.replicate 24 0 ++ #[1] ++ Array.replicate 8 0 ++ #[1, 0, 0, 1, 0]
  unless execute fresh [2, 11, 99] == some
      (freshBytes, [.invoke, .input 2, .invoke, .input 11], [99], #[77], 4, 91, 9, true, true) do
    throwError "signing miss lost ordered draws, signature, challenge, histories, external frame, scratch release or time bound"
  unless execute collision [2, 11, 99] == some
      (hitBytes, [.invoke, .input 2, .invoke, .input 11], [99], #[77], 4, 91, 9, true, true) do
    throwError "signing collision skipped a draw or overwrote cached zero, shadowed entry, affine explanation or histories"
  unless execute finalSlot [65535, 2] == some
      (finalBytes, [.invoke, .input 65535, .invoke, .input 2], [], #[77], 4, 91, 9, true, true) do
    throwError "signing at final capacity lost modular arithmetic, insertion, append or flags"
  unless execute empty [0, 0] == some
      (emptyBytes, [.invoke, .input 0, .invoke, .input 0], [], #[77], 4, 91, 9, true, true) do
    throwError "zero signing failed on empty stores"
  unless execute fresh [2] == none && execute collision [2] == none do
    throwError "accepted signing succeeded without its response draw"
  for (args, c, z, expected) in [(fresh, 2, 11, freshBytes), (collision, 2, 11, hitBytes),
      (finalSlot, 65535, 2, finalBytes), (empty, 0, 0, emptyBytes)] do
    unless executeSampled args c z == some (expected, true, true) do
      throwError "deterministic signing stages did not compose to the complete expected state"
  let fullResult := (Caliper.run .unit RandomTape.zero 1000000 deterministic.program.code
    ((Sampled.input layout).representation.initial fullHit)).map (fun result => result.1.bufs 0)
  unless fullResult == some #[23, 11, 4, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12, 5, 6, 1, 0, 13, 14,
      8, 9, 3, 1, 15, 16, 4, 5, 7, 1, 0, 0, 1, 11, 65534, 2, 7, 7, 1, 1] do
    throwError "full-table deterministic signing collision did not preserve the original entries and append both histories"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Sampled.implementation, ``Sampled.bounded, ``Sampled.names, ``Sampled.buffers, ``Sampled.resources,
      ``Sampled.source, ``Sampled.signedState, ``Sampled.reserved_admissible, ``Sampling.sample_refines, ``Sampling.refines,
      ``Sampling.time_bound, ``Sampling.code_bound, ``Sampling.names, ``Sampling.descriptionFits, ``Sampling.resources,
      ``Sampling.erase, ``Sampling.uniform, ``Sampling.source_original, ``Sampling.input_valid, ``Sampling.reserved_ready,
      ``deterministicBound, ``deterministicNamed, ``deterministicBuffers, ``refined, ``timed, ``stored, ``named, ``accepted, ``memory, ``zeroAdmission] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMSigning
