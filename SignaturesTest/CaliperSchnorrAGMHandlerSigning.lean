import Proofs.Runtime.Caliper.SchnorrAGMHandlerSigningMemory
import Proofs.Runtime.Caliper.EncodedConstant
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMHandlerSigning
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
private def signing : CaliperBackend.SchnorrAGM.Signing.Histories.Layouts 16 Nat (Word 16) (Word 16) 1 2 where
  signing := { scheme := scheme, storageFits := by decide }
  counterFits := by decide

private def scale : Implementation .unit signing.signing.arithmetic.scaleArgs scheme.point (fun input => input.1 • input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput signing.signing.arithmetic.scaleArgs.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput scheme.point.representation
      (fun input => ⟨input.val.1 * input.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit signing.signing.arithmetic.points scheme.point (fun input => input.1 - input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput signing.signing.arithmetic.points.representation
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

private def layout : CaliperBackend.SchnorrAGM.Handler.Layouts 16 Nat (Word 16) (Word 16) 1 2 65535 where
  scheme := scheme
  groups := 2
  rows := 3
  coefficients := 4
  rangeFits := by decide
  counterFits := by decide
  groupCountFits := by decide
  rowCountFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

open CaliperBackend.SchnorrAGM.Handler.SigningComponent
private def program := code layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
private def sourceModel := source layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) sampleSource
private def timeLimit := timeBudget layout 6 6 118 4
private def codeLimit := codeBudget layout 27 27 631 20
private def nameLimit := Sampling.nameBudget 3 3
private theorem refined : Interactive.Refines port .unit layout.signingInput.representation layout.scalarOutput.representation sourceModel program :=
  refines layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampleCorrect
private theorem timed : Interactive.TimeBound port .unit layout.signingInput.representation program timeLimit :=
  time_bound layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port
    sampleCorrect scaleBound subBound negateBound sampleTime
private theorem stored : (program.lower port).descriptionWords ≤ codeLimit :=
  code_bound layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
    scaleBound subBound negateBound sampleWords
private theorem named : WordIO.NamesAccounted (program.lower port) nameLimit :=
  names (primitiveNames := 3) (sampleSlots := 3) layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
    scaleNames.accounted subNames.accounted negateNames.accounted sampleNames
private theorem fitting : (program.lower port).DescriptionFits :=
  descriptionFits layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
    sampleFits sampleNames (by decide)
private theorem boundedBuffers : (program.lower port).memBound ≤ 10 :=
  buffers (slots := 3) (sampleSlots := 3) layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler sampleNames

private theorem valid_iff (g pk : Word 16) (message : Nat) (groups : List (Word 16)) (rows : List (List (Word 16)))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.signingInput.valid ((message, groups, rows), (g, pk), entries, basis, signed, malformed, bad) ↔
      (message < 256 ∧ groups.length ≤ 2 ∧ (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4) ∧
        (entries.length ≤ 4 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 4 ∧ signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧
        (groups.isEmpty = true → entries.length ≤ 3 ∧ basis.length < 4 ∧ signed.length < 2) := by
  change (((message < 256 ∧ (groups.length ≤ 2 ∧ ∀ _ ∈ groups, True) ∧
    (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4 ∧ ∀ _ ∈ row, True)) ∧ (True ∧ True) ∧
    (entries.length ≤ 4 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 4 ∧ ∀ _ ∈ basis, True ∧ True) ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _) ↔ _
  simp only [true_and, and_true, implies_true, and_assoc]
  rfl

private def fresh (g pk : Word 16) : layout.signingInput.Value :=
  ⟨((7, [], [[], [9, 8, 7, 6], [5]]), (g, pk), [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1)], [3], false, false), by rw [valid_iff]; decide⟩
private def collision (bad : Bool) : layout.signingInput.Value :=
  ⟨((7, [], []), (3, 5), [((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12))],
    [(5, 7), (1, 0), (0, 1)], [7], true, bad), by rw [valid_iff]; decide⟩
private def finalSlot : layout.signingInput.Value :=
  ⟨((255, [], [[65535]]), (5, 3), [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14))],
    [(1, 0), (0, 1), (5, 7)], [9], false, true), by rw [valid_iff]; decide⟩
private def empty : layout.signingInput.Value :=
  ⟨((0, [], [[], [], []]), (5, 3), [], [], [], true, false), by rw [valid_iff]; decide⟩
private def full : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)) :=
  [((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14)), ((8, 9), (3, true, 15, 16))]
private def refused (g pk : Word 16) (malformed bad : Bool) : layout.signingInput.Value :=
  ⟨((7, [4, 7], [[2, 3, 4, 5], [], [6]]), (g, pk), full, [(5, 7), (1, 0), (0, 1), (11, 65534)], [7, 7], malformed, bad), by
    rw [valid_iff]
    change (7 < 256 ∧ 2 ≤ 2 ∧ (3 ≤ 3 ∧ _) ∧ (4 ≤ 4 ∧ _) ∧ 4 ≤ 4 ∧ 2 ≤ 2 ∧ _) ∧ (false = true → _)
    decide⟩

example : ¬ layout.signingInput.valid ((256, [], []), (1, 1), [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.signingInput.valid ((0, [], []), (1, 1), [], [], [1, 2], false, false) := by rw [valid_iff]; decide
example : ¬ layout.signingInput.valid ((0, [], []), (1, 1), full, [], [], false, false) := by rw [valid_iff]; decide

private def emptyListsLayout : CaliperBackend.SchnorrAGM.Handler.Layouts 16 Nat (Word 16) (Word 16) 1 2 65535 :=
  { layout with
    groups := 0
    rows := 0
    coefficients := 0
    groupCountFits := by decide
    rowCountFits := by decide
    coefficientCountFits := by decide
    storageFits := by decide }
private def emptyLists : emptyListsLayout.signingInput.Value :=
  ⟨((0, [], []), (5, 3), [], [], [], true, false), by
    change ((0 < 256 ∧ (0 ≤ 0 ∧ _) ∧ (0 ≤ 0 ∧ _)) ∧ (True ∧ True) ∧ (0 ≤ 4 ∧ _) ∧
      (0 ≤ 4 ∧ _) ∧ (0 ≤ 2 ∧ _) ∧ True ∧ True) ∧ (true = true → 0 ≤ 3 ∧ 0 < 4 ∧ 0 < 2)
    simp only [List.not_mem_nil, false_implies, implies_true, and_true]
    decide⟩
private def emptyListsProgram := code emptyListsLayout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler

private theorem memory (tape : RandomTape 16) (args : layout.signingInput.Value) (before : State 16)
    (holds : layout.signingInput.representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute port .unit tape before)) :
    finished.time ≤ timeLimit ∧ ∃ answer ∈ support (sourceModel args),
      layout.scalarOutput.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (program.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((program.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (program.lower port).memBound) ≤
            5 * codeLimit + 4 * nameLimit + registers + 3 * buffers + before.liveMem buffers + timeLimit := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    resources layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port
      sampleCorrect scaleBound subBound negateBound sampleTime sampleWords scaleNames.accounted subNames.accounted negateNames.accounted
      sampleNames tape args before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def execute (args : layout.signingInput.Value) (replies : List (Word 16)) := do
  let initial := layout.signingInput.representation.initial args
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ timeLimit))

open Lean in
run_cmd do
  let check := fun args replies bytes trace remaining =>
    execute args replies == some (bytes, trace, remaining, #[77], 4, 91, 9, true, true)
  for (g, pk, commitment) in ([(3, 5, 23), (5, 3, 49), (65535, 0, 65525)] : List (Word 16 × Word 16 × Word 16)) do
    let freshBytes : Array (Word 16) := #[11, 1, commitment, g, pk, 2, 7, commitment, 2, 0, 0, 0, 5, 6, 1, 1, 13, 14] ++ Array.replicate 12 0 ++
      #[3, 1, 0, 0, 1, 11, 65534, 0, 0, 2, 3, 7, 0, 0]
    unless check (fresh g pk) [2, 11, 99] freshBytes [.invoke, .input 2, .invoke, .input 11] [99] do
      throwError "common-store signing did not use and restore its runtime configuration or preserve its state/frame"
    unless execute (fresh g pk) [] == none && execute (fresh g pk) [2] == none do
      throwError "accepted common-store signing succeeded without both draws"
    for malformed in [false, true] do
      for bad in [false, true] do
        let expected : Array (Word 16) := #[0, 0, 0, g, pk, 4, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12,
          5, 6, 1, 0, 13, 14, 8, 9, 3, 1, 15, 16, 4, 5, 7, 1, 0, 0, 1, 11, 65534, 2, 7, 7, 1, if bad then 1 else 0]
        unless check (refused g pk malformed bad) [88] expected [] [88] && check (refused g pk malformed bad) [] expected [] [] do
          throwError "common-store rejection sampled, needed free slots, lost configuration/flags or failed to release scratch"
  for bad in [false, true] do
    let hitBytes : Array (Word 16) := #[11, 1, 23, 3, 5, 2, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12] ++ Array.replicate 12 0 ++
      #[4, 5, 7, 1, 0, 0, 1, 11, 65534, 2, 7, 7, 1, if bad then 1 else 0]
    unless check (collision bad) [2, 11, 99] hitBytes [.invoke, .input 2, .invoke, .input 11] [99] do
      throwError "common-store collision skipped a draw or changed cached zero, duplicates or flags"
    unless execute (collision bad) [2] == none do
      throwError "common-store cache collision skipped its second draw"
  let finalBytes : Array (Word 16) := #[2, 1, 13, 5, 3, 4, 255, 13, 65535, 0, 0, 0, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12,
    5, 6, 1, 0, 13, 14, 4, 1, 0, 0, 1, 5, 7, 2, 1, 2, 9, 255, 0, 1]
  unless check finalSlot [65535, 2] finalBytes [.invoke, .input 65535, .invoke, .input 2] [] do
    throwError "common-store signing at final capacity lost runtime arithmetic, histories or configuration"
  let emptyBytes : Array (Word 16) := #[0, 1, 0, 5, 3, 1] ++ Array.replicate 24 0 ++ #[1] ++ Array.replicate 8 0 ++ #[1, 0, 0, 1, 0]
  unless check empty [0, 0] emptyBytes [.invoke, .input 0, .invoke, .input 0] [] do
    throwError "common-store zero signature or empty stores encoded incorrectly"
  let emptyResult := (WordIO.run .unit RandomTape.zero 1000000 (emptyListsProgram.lower port)
    (emptyListsLayout.signingInput.representation.initial emptyLists) [0, 0]).map
      (fun result => (result.state.bufs 0, result.trace, result.remaining))
  unless emptyResult == some (emptyBytes, [.invoke, .input 0, .invoke, .input 0], []) do
    throwError "zero group/row/coefficient capacities broke common-store signing"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``prepare, ``finish, ``refines, ``erase, ``reply_config, ``time_bound, ``code_bound, ``names,
      ``buffers, ``descriptionFits, ``resources, ``source_original, ``input_valid, ``reserved_input,
      ``Sampling.buffers, ``CaliperBackend.SchnorrAGM.SigningDispatch.buffers,
      ``refined, ``timed, ``stored, ``named, ``fitting, ``boundedBuffers, ``memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMHandlerSigning
