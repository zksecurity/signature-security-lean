import Signatures.Runtime.Caliper.SchnorrAGMHandlerMemory
import Signatures.Runtime.Caliper.UniformSamplingBounds
import Signatures.Runtime.Caliper.EncodedConstant
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMHandler
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


private def mul : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 * value.2) := scale
private def add : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .add (by decide)).viewInput scheme.affine.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput scheme.scalar.representation
      (fun input => ⟨input.val.1 + input.val.2, trivial⟩) (fun _ => rfl)
private theorem addBound : add.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem addNames : NamesBound add.program.code 3 := ⟨by decide, by decide⟩

open CaliperBackend.SchnorrAGM.Handler
private def operations : Operations layout where
  zeroValid := trivial
  mul := mul
  add := add
  scale := scale
  sub := sub
  negate := negate
  slots := 3
  mulNames := scaleNames
  addNames := addNames
  scaleNames := scaleNames
  subNames := subNames
  negateNames := negateNames
  reserve := by decide
private def budget : Budget layout operations where
  mulTime := 6
  mulWords := 27
  addTime := 6
  addWords := 27
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  negateTime := 118
  negateWords := 631
  mul := scaleBound
  add := addBound
  scale := scaleBound
  sub := subBound
  negate := negateBound

private def sampler := UniformSampling.code (w := 16) 65535 (by decide) (by decide) (65535 : Fin 65536)
private def sampleValue (value : (UniformSampling.output (w := 16) 65535 (by decide) (by decide) (65535 : Fin 65536)).Value) :
    scheme.scalar.Value := ⟨BitVec.ofNat 16 value.val.val, trivial⟩
private def sampleSource := sampleValue <$> UniformSampling.source (w := 16) 65535 (by decide) (by decide) (65535 : Fin 65536)
private theorem sampleCorrect : Interactive.Refines layout.random.port .unit (PairSampling.input 16).representation scheme.scalar.representation
    (fun _ => sampleSource) sampler :=
  (UniformSampling.refines 65535 (by decide) (by decide) (65535 : Fin 65536)).viewOutput scheme.scalar.representation sampleValue (fun _ => rfl)
private theorem sampleTime : Interactive.TimeBound layout.random.port .unit (PairSampling.input 16).representation sampler 26 :=
  UniformSampling.time_bound 65535 (by decide) (by decide) (65535 : Fin 65536)
private theorem sampleWords : (sampler.lower layout.random.port).descriptionWords ≤ 125 :=
  UniformSampling.code_words 65535 (by decide) (by decide) (65535 : Fin 65536)
private theorem sampleNames : WordIO.NamesBound (sampler.lower layout.random.port) 3 :=
  UniformSampling.names 65535 (by decide) (by decide) (65535 : Fin 65536)
private theorem sampleFits : (sampler.lower layout.random.port).DescriptionFits :=
  UniformSampling.descriptionFits 65535 (by decide) (by decide) (65535 : Fin 65536)
private def program := code layout operations sampler
private def sourceModel := source layout operations sampleSource
private def timeLimit := timeBudget layout operations budget 26
private def codeLimit := codeBudget layout operations budget 125
private def nameLimit := nameBudget layout operations 3
private theorem refined : Interactive.Refines layout.random.port .unit (Dispatch.input layout) (Dispatch.output layout) sourceModel program :=
  refines layout operations sampleCorrect
private theorem timed : Interactive.TimeBound layout.random.port .unit (Dispatch.input layout) program timeLimit :=
  time_bound layout operations sampleCorrect budget sampleTime
private theorem stored : (program.lower layout.random.port).descriptionWords ≤ codeLimit := code_bound layout operations budget sampleWords
private theorem named : WordIO.NamesAccounted (program.lower layout.random.port) nameLimit := names layout operations sampleNames
private theorem fitting : (program.lower layout.random.port).DescriptionFits := descriptionFits layout operations sampleFits sampleNames (by decide)

private theorem signing_valid_iff (g pk : Word 16) (message : Nat) (groups : List (Word 16)) (rows : List (List (Word 16)))
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


private theorem hash_valid_iff (g pk : Word 16) (message : Nat) (groups : List (Word 16)) (rows : List (List (Word 16)))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.hashInput.valid ((message, groups, rows), (g, pk), entries, basis, signed, malformed, bad) ↔
      (message < 256 ∧ groups.length ≤ 2 ∧ (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4) ∧
        (entries.length ≤ 4 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 4 ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256)) ∧
        layout.hash.admissible (message, groups, rows, entries, basis, signed, malformed, bad) := by
  change (((message < 256 ∧ (groups.length ≤ 2 ∧ ∀ _ ∈ groups, True) ∧
    (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4 ∧ ∀ _ ∈ row, True)) ∧ (True ∧ True) ∧
    (entries.length ≤ 4 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 4 ∧ ∀ _ ∈ basis, True ∧ True) ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _) ↔ _
  simp only [and_true, true_and, implies_true, and_assoc]
  rfl

private def fresh (g pk : Word 16) : layout.signingInput.Value :=
  ⟨((7, [], [[], [9, 8, 7, 6], [5]]), (g, pk), [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1)], [3], false, false), by rw [signing_valid_iff]; decide⟩
private def freshHash : layout.hashInput.Value :=
  ⟨((7, [23], [[9, 8, 7, 6]]), (3, 5), [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1)], [3], false, false), by rw [hash_valid_iff]; decide⟩
private def hitHash : layout.hashInput.Value :=
  ⟨((7, [23], [[5, 6, 7, 8]]), (3, 5), [((7, 23), (0, true, 9, 8))], [(1, 0), (0, 1)], [3], false, false), by rw [hash_valid_iff]; decide⟩
private theorem random_valid_iff (g pk : Word 16) (n : Nat) (groups : List (Word 16)) (rows : List (List (Word 16)))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.randomInput.valid ((n, groups, rows), (g, pk), entries, basis, signed, malformed, bad) ↔
      n < 65536 ∧ groups.length ≤ 2 ∧ (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4) ∧
        (entries.length ≤ 4 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 4 ∧ signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256 := by
  change ((n < 65536 ∧ (groups.length ≤ 2 ∧ ∀ _ ∈ groups, True) ∧
    (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4 ∧ ∀ _ ∈ row, True)) ∧ (True ∧ True) ∧
    (entries.length ≤ 4 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 4 ∧ ∀ _ ∈ basis, True ∧ True) ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ↔ _
  simp only [implies_true, true_and, and_true, and_assoc]
private def random (n : Fin 65536) : layout.randomInput.Value :=
  ⟨((n.val, [4, 7], [[], [1, 2, 3, 4], [5]]), (3, 5), [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1)], [3], false, true), by
    rw [random_valid_iff]
    exact ⟨n.isLt, by decide⟩⟩
private def full : SchnorrAGM.Native.EncodedState (Word 16) (Word 16) Nat :=
  ([((7, 23), (0, true, 9, 10)), ((7, 23), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14)), ((8, 9), (3, true, 15, 16))],
    [(5, 7), (1, 0), (0, 1), (11, 65534)], [7, 7], false, true)
private def refusedSign : layout.signingInput.Value :=
  ⟨((7, [4, 7], [[2, 3, 4, 5], [], [6]]), (3, 5), full), by rw [signing_valid_iff]; decide⟩
private def refusedHash : layout.hashInput.Value :=
  ⟨((7, [4, 7], [[2, 3, 4, 5], [], [6]]), (3, 5), full), by rw [hash_valid_iff]; decide⟩

private theorem memory (tape : RandomTape 16) (args : Dispatch.Input layout) (before : State 16)
    (holds : (Dispatch.input layout).Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute layout.random.port .unit tape before)) :
    finished.time ≤ timeLimit ∧ ∃ answer ∈ support (sourceModel args),
      (Dispatch.output layout).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (program.lower layout.random.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((program.lower layout.random.port).staticWords registers buffers : Int) + between.liveMem (max buffers (program.lower layout.random.port).memBound) ≤
            5 * codeLimit + 4 * nameLimit + registers + 3 * buffers + before.liveMem buffers + timeLimit := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    resources layout operations budget sampleCorrect sampleTime sampleWords sampleNames tape args before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def execute (args : Dispatch.Input layout) (replies : List (Word 16)) := do
  let initial := (Dispatch.input layout).initial args
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower layout.random.port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0), decide (result.time ≤ timeLimit))

open Lean in
run_cmd do
  let check := fun args replies bytes trace remaining =>
    execute args replies == some (bytes, trace, remaining, #[77], 4, 91, 9, true, true)
  let signingRequest : Array (Word 16) := #[7, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 9, 8, 7, 6, 1, 5, 0, 0, 0]
  let hashRequest : Array (Word 16) := #[7, 1, 23, 0, 1, 4, 9, 8, 7, 6] ++ Array.replicate 10 0
  let hitRequest : Array (Word 16) := #[7, 1, 23, 0, 1, 4, 5, 6, 7, 8] ++ Array.replicate 10 0
  let refusedRequest : Array (Word 16) := #[7, 2, 4, 7, 3, 4, 2, 3, 4, 5, 0, 0, 0, 0, 0, 1, 6, 0, 0, 0]
  for (g, pk, commitment) in ([(3, 5, 23), (5, 3, 49), (65535, 0, 65525)] : List (Word 16 × Word 16 × Word 16)) do
    let bytes : Array (Word 16) := #[1, 1, 11, 1, commitment, g, pk, 2, 7, commitment, 2, 0, 0, 0, 5, 6, 1, 1, 13, 14] ++ Array.replicate 12 0 ++
      #[3, 1, 0, 0, 1, 11, 65534, 0, 0, 2, 3, 7, 0, 0] ++ signingRequest
    unless check (.inr (.inr (fresh g pk))) [65535, 2, 65535, 11, 99] bytes [.output 65535, .invoke, .input 65535, .input 2, .output 65535, .invoke, .input 65535, .input 11] [99] do
      throwError "combined signing lost its request, runtime configuration, trace or caller frame"
    unless execute (.inr (.inr (fresh g pk))) [] == none && execute (.inr (.inr (fresh g pk))) [65535, 2, 65535] == none do
      throwError "combined signing accepted missing draws"
  let hashBytes : Array (Word 16) := #[1, 0, 2, 0, 0, 3, 5, 2, 7, 23, 2, 1, 9, 8, 5, 6, 1, 1, 13, 14] ++ Array.replicate 12 0 ++
    #[2, 1, 0, 0, 1, 0, 0, 0, 0, 1, 3, 0, 0, 0] ++ hashRequest
  unless check (.inr (.inl freshHash)) [65535, 2, 99] hashBytes [.output 65535, .invoke, .input 65535, .input 2] [99] do
    throwError "combined fresh hash lost affine arithmetic, tags, state or original request"
  let hitBytes : Array (Word 16) := #[1, 0, 0, 0, 0, 3, 5, 1, 7, 23, 0, 1, 9, 8] ++ Array.replicate 18 0 ++
    #[2, 1, 0, 0, 1, 0, 0, 0, 0, 1, 3, 0, 0, 0] ++ hitRequest
  unless check (.inr (.inl hitHash)) [88] hitBytes [] [88] do
    throwError "combined cache hit sampled or lost the request's coefficient row"
  for n in ([0, 5, 65535] : List (Fin 65536)) do
    let request : Array (Word 16) := #[BitVec.ofNat 16 n.val, 2, 4, 7, 3, 0, 0, 0, 0, 0, 4, 1, 2, 3, 4, 1, 5, 0, 0, 0]
    let bytes : Array (Word 16) := #[0, BitVec.ofNat 16 n.val, 0, 0, 3, 5, 1, 5, 6, 1, 1, 13, 14] ++ Array.replicate 18 0 ++
      #[2, 1, 0, 0, 1, 0, 0, 0, 0, 1, 3, 0, 1, 1] ++ request ++ #[0]
    unless check (.inl (random n)) [BitVec.ofNat 16 n.val, BitVec.ofNat 16 n.val, 99] bytes [.output (BitVec.ofNat 16 n.val), .invoke, .input (BitVec.ofNat 16 n.val), .input (BitVec.ofNat 16 n.val)] [99] do
      throwError "combined randomness changed its range, request, state or outer padding"
    unless execute (.inl (random n)) [] == none do throwError "combined randomness accepted a missing reply"
  let refusedBytes : Array (Word 16) := #[0, 0, 0, 3, 5, 4, 7, 23, 0, 1, 9, 10, 7, 23, 8, 1, 11, 12,
    5, 6, 1, 0, 13, 14, 8, 9, 3, 1, 15, 16, 4, 5, 7, 1, 0, 0, 1, 11, 65534, 2, 7, 7, 1, 1] ++ refusedRequest
  unless check (.inr (.inl refusedHash)) [88] (#[1, 0] ++ refusedBytes) [] [88] &&
      check (.inr (.inr refusedSign)) [88] (#[1, 1] ++ refusedBytes) [] [88] do
    throwError "combined malformed rejection sampled, required free space or lost the request"
  unless execute (.inr (.inl freshHash)) [] == none do throwError "combined fresh hash accepted a missing draw"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Interactive.Prefix.refines, ``Interactive.Prefix.time_bound, ``Interactive.Prefix.code_bound,
      ``Dispatch.refines, ``Dispatch.time_bound, ``Dispatch.code_bound, ``CaliperBackend.SchnorrAGM.Handler.Dispatch.names, ``Dispatch.descriptionFits,
      ``refines, ``time_bound, ``code_bound, ``names, ``descriptionFits, ``resources, ``source_original, ``source_request,
      ``refined, ``timed, ``stored, ``named, ``fitting, ``memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMHandler
