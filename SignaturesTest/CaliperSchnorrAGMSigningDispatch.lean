import Signatures.Runtime.Caliper.SchnorrAGMSigningDispatchMemory
import Signatures.Runtime.Caliper.SchnorrAGMSigningDispatchSource
import Signatures.Runtime.Caliper.EncodedConstant
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMSigningDispatch
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

private def layout : CaliperBackend.SchnorrAGM.SigningDispatch.Layouts 16 Nat (Word 16) (Word 16) 1 2 where
  signing := signing
  groups := 2
  rows := 3
  coefficients := 4
  groupCountFits := by decide
  rowCountFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

open CaliperBackend.SchnorrAGM.SigningDispatch
private def program := code layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
private def source := CaliperBackend.SchnorrAGM.SigningDispatch.source layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) sampleSource
private def timeLimit := timeBudget layout 6 6 118 4
private def codeLimit := codeBudget layout 27 27 631 20
private def nameLimit := Sampling.nameBudget 3 3
private theorem refined : Interactive.Refines port .unit layout.input.representation layout.output.representation source program :=
  refines layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampleCorrect
private theorem timed : Interactive.TimeBound port .unit layout.input.representation program timeLimit :=
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

private theorem valid_iff (groups : List (Word 16)) (rows : List (List (Word 16))) (g pk : Word 16) (message : Nat)
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.input.valid (groups, rows, g, pk, message, entries, basis, signed, malformed, bad) ↔
      (groups.length ≤ 2 ∧ (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4) ∧
        message < 256 ∧ (entries.length ≤ 4 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 4 ∧ signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧
        (groups.isEmpty = true → entries.length ≤ 3 ∧ basis.length < 4 ∧ signed.length < 2) := by
  change (((groups.length ≤ 2 ∧ ∀ group ∈ groups, True) ∧
    (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4 ∧ ∀ coefficient ∈ row, True) ∧ True ∧ True ∧ message < 256 ∧
    (entries.length ≤ 4 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 4 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _) ↔ _
  simp only [true_and, and_true, implies_true, and_assoc]
  rfl

private def fresh : layout.input.Value :=
  ⟨([], [[], [9, 8, 7, 6], [5]], 3, 5, 7, [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1)], [3], false, false), by rw [valid_iff]; decide⟩
private def collision : layout.input.Value :=
  ⟨([], [], 3, 5, 7, [((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12))],
    [(5, 7), (1, 0), (0, 1)], [7], true, true), by rw [valid_iff]; decide⟩
private def finalSlot : layout.input.Value :=
  ⟨([], [[65535]], 5, 3, 255, [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14))],
    [(1, 0), (0, 1), (5, 7)], [9], false, true), by rw [valid_iff]; decide⟩
private def empty : layout.input.Value :=
  ⟨([], [[], [], []], 5, 3, 0, [], [], [], true, false), by rw [valid_iff]; decide⟩
private def full : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)) :=
  [((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14)), ((8, 9), (3, true, 15, 16))]
private def refused (malformed bad : Bool) : layout.input.Value :=
  ⟨([4, 7], [[2, 3, 4, 5], [], [6]], 3, 5, 7, full, [(5, 7), (1, 0), (0, 1), (11, 65534)], [7, 7], malformed, bad), by
    rw [valid_iff]
    change (2 ≤ 2 ∧ (3 ≤ 3 ∧ _) ∧ 7 < 256 ∧ (4 ≤ 4 ∧ _) ∧ 4 ≤ 4 ∧ 2 ≤ 2 ∧ _) ∧ (false = true → _)
    decide⟩

example : ¬ layout.input.valid ([], [], 1, 1, 256, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([], [], 1, 1, 0, [], [], [1, 2], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([], [], 1, 1, 0, full, [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1, 2, 3], [], 1, 1, 0, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [[], [], [], []], 1, 1, 0, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [[1, 2, 3, 4, 5]], 1, 1, 0, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [], 1, 1, 0, [((256, 0), (0, false, 0, 0))], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [], 1, 1, 0, [], [], [256], false, false) := by rw [valid_iff]; decide

private def emptyListsLayout : CaliperBackend.SchnorrAGM.SigningDispatch.Layouts 16 Nat (Word 16) (Word 16) 1 2 :=
  { layout with
    groups := 0
    rows := 0
    coefficients := 0
    groupCountFits := by decide
    rowCountFits := by decide
    coefficientCountFits := by decide
    storageFits := by decide }
private def emptyLists : emptyListsLayout.input.Value :=
  ⟨([], [], 5, 3, 0, [], [], [], true, false), by
    change ((0 ≤ 0 ∧ _) ∧ (0 ≤ 0 ∧ _) ∧ True ∧ True ∧ 0 < 256 ∧ (0 ≤ 4 ∧ _) ∧
      (0 ≤ 4 ∧ _) ∧ (0 ≤ 2 ∧ _) ∧ True ∧ True) ∧ (true = true → 0 ≤ 3 ∧ 0 < 4 ∧ 0 < 2)
    simp only [List.not_mem_nil, false_implies, implies_true, and_true]
    decide⟩
private def emptyListsProgram := code emptyListsLayout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
private def emptyRowsLayout : CaliperBackend.SchnorrAGM.SigningDispatch.Layouts 16 Nat (Word 16) (Word 16) 1 2 :=
  { layout with coefficients := 0, coefficientCountFits := by decide, storageFits := by decide }
private def emptyRows : emptyRowsLayout.input.Value :=
  ⟨([], [[], [], []], 5, 3, 0, [], [], [], true, false), by
    change ((0 ≤ 2 ∧ _) ∧ (3 ≤ 3 ∧ ∀ row ∈ ([[], [], []] : List (List (Word 16))), row.length ≤ 0 ∧ ∀ coefficient ∈ row, True) ∧ True ∧ True ∧ 0 < 256 ∧ (0 ≤ 4 ∧ _) ∧
      (0 ≤ 4 ∧ _) ∧ (0 ≤ 2 ∧ _) ∧ True ∧ True) ∧ (true = true → 0 ≤ 3 ∧ 0 < 4 ∧ 0 < 2)
    simp only [List.not_mem_nil, false_implies, implies_true, and_true]
    decide⟩
private def emptyRowsProgram := code emptyRowsLayout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
private def zeroScheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 0 where
  scalar := scheme.scalar
  point := scheme.point
  message := scheme.message
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def zeroSigning : Histories.Layouts 16 Nat (Word 16) (Word 16) 1 0 where
  signing := { scheme := zeroScheme, storageFits := by decide }
  counterFits := by decide
private def zeroQueries : CaliperBackend.SchnorrAGM.SigningDispatch.Layouts 16 Nat (Word 16) (Word 16) 1 0 where
  signing := zeroSigning
  groups := 1
  rows := 0
  coefficients := 0
  groupCountFits := by decide
  rowCountFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide
private def zeroRefused : zeroQueries.input.Value :=
  ⟨([7], [], 3, 5, 0, [((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12))], [(1, 0), (0, 1)], [], false, true), by
    refine ⟨⟨⟨by decide, fun _ _ => trivial⟩, ⟨by decide, by simp⟩,
      trivial, trivial, by change 0 < 256; decide, ⟨by decide, ?_⟩, ⟨by decide, fun _ _ => ⟨trivial, trivial⟩⟩,
      ⟨by decide, by simp⟩, trivial, trivial⟩, ?_⟩
    · intro entry member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨⟨by change 7 < 256; decide, trivial⟩, trivial, trivial, trivial, trivial⟩
    · intro impossible
      contradiction⟩
private def zeroProgram := code zeroQueries trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port sampler
private theorem zeroAdmission (args : CaliperBackend.SchnorrAGM.SigningDispatch.Input Nat (Word 16) (Word 16)) (emptyGroups : args.1 = []) :
    ¬ zeroQueries.input.valid args := by
  intro valid
  have empty : shape args = true := by simp only [shape, emptyGroups, List.isEmpty_nil]
  exact Nat.not_lt_zero _ (valid.2 empty).2.2

private theorem memory (tape : RandomTape 16) (args : layout.input.Value) (before : State 16)
    (holds : layout.input.representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute port .unit tape before)) :
    finished.time ≤ timeLimit ∧ ∃ answer ∈ support (source args),
      layout.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (program.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((program.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (program.lower port).memBound) ≤
            5 * codeLimit + 4 * nameLimit + registers + 3 * buffers + before.liveMem buffers + timeLimit := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    resources layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) port
      sampleCorrect scaleBound subBound negateBound sampleTime sampleWords scaleNames.accounted subNames.accounted negateNames.accounted
      sampleNames tape args before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def execute (args : layout.input.Value) (replies : List (Word 16)) := do
  let initial := layout.input.representation.initial args
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
  let freshBytes : Array (Word 16) := #[11, 1, 23, 2, 7, 23, 2, 0, 0, 0, 5, 6, 1, 1, 13, 14] ++ Array.replicate 12 0 ++
    #[3, 1, 0, 0, 1, 11, 65534, 0, 0, 2, 3, 7, 0, 0]
  let hitBytes : Array (Word 16) := #[11, 1, 23, 2, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12] ++ Array.replicate 12 0 ++
    #[4, 5, 7, 1, 0, 0, 1, 11, 65534, 2, 7, 7, 1, 1]
  let finalBytes : Array (Word 16) := #[2, 1, 13, 4, 255, 13, 65535, 0, 0, 0, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12,
    5, 6, 1, 0, 13, 14, 4, 1, 0, 0, 1, 5, 7, 2, 1, 2, 9, 255, 0, 1]
  let emptyBytes : Array (Word 16) := #[0, 1, 0, 1] ++ Array.replicate 24 0 ++ #[1] ++ Array.replicate 8 0 ++ #[1, 0, 0, 1, 0]
  let check := fun args replies bytes trace remaining =>
    execute args replies == some (bytes, trace, remaining, #[77], 4, 91, 9, true, true)
  unless check fresh [2, 11, 99] freshBytes [.invoke, .input 2, .invoke, .input 11] [99] do
    throwError "accepted signing failed with arbitrary ignored coefficient rows"
  unless check collision [2, 11, 99] hitBytes [.invoke, .input 2, .invoke, .input 11] [99] do
    throwError "signing collision skipped a draw or changed cached zero, duplicate entries or flags"
  unless check finalSlot [65535, 2] finalBytes [.invoke, .input 65535, .invoke, .input 2] [] do
    throwError "signing at final capacity lost arithmetic, histories or reply encoding"
  unless check empty [0, 0] emptyBytes [.invoke, .input 0, .invoke, .input 0] [] do
    throwError "empty stores or zero-valued signature encoded incorrectly"
  unless execute fresh [2] == none && execute collision [2] == none do
    throwError "accepted request succeeded without both draws"
  for malformed in [false, true] do
    for bad in [false, true] do
      let expected : Array (Word 16) := #[0, 0, 0, 4, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12,
        5, 6, 1, 0, 13, 14, 8, 9, 3, 1, 15, 16, 4, 5, 7, 1, 0, 0, 1, 11, 65534, 2, 7, 7, 1, if bad then 1 else 0]
      unless check (refused malformed bad) [88] expected [] [88] && check (refused malformed bad) [] expected [] [] do
        throwError "rejection sampled, needed free slots, lost histories/bad or failed to set malformed"
  let executeSmall := fun program initial replies =>
    (WordIO.run .unit RandomTape.zero 1000000 (program.lower port) initial replies).map
      (fun result => (result.state.bufs 0, result.trace, result.remaining))
  unless executeSmall emptyListsProgram (emptyListsLayout.input.representation.initial emptyLists) [0, 0] ==
      some (emptyBytes, [.invoke, .input 0, .invoke, .input 0], []) do
    throwError "zero group/row/coefficient capacities broke the accepted branch"
  unless executeSmall emptyRowsProgram (emptyRowsLayout.input.representation.initial emptyRows) [0, 0] ==
      some (emptyBytes, [.invoke, .input 0, .invoke, .input 0], []) do
    throwError "zero coefficient capacity rejected represented empty rows"
  unless executeSmall zeroProgram (zeroQueries.input.representation.initial zeroRefused) [] ==
      some (#[0, 0, 0, 2, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12, 2, 1, 0, 0, 1, 0, 1, 1], [], []) do
    throwError "zero signing allowance prevented malformed rejection with full stores"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CaliperBackend.SchnorrAGM.SigningDispatch.test, ``selector, ``accept, ``wrap, ``reject,
      ``refines, ``time_bound, ``code_bound, ``names, ``descriptionFits, ``resources,
      ``source_original, ``input_valid, ``reserved_input, ``refined, ``timed, ``stored, ``named, ``fitting, ``memory, ``zeroAdmission] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMSigningDispatch
