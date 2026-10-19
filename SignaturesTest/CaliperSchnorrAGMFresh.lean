import Signatures.Runtime.Caliper.SchnorrAGMCacheMemory
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMFresh

-- Executed modular-word addition is a wiring fixture, not a cryptographic
-- field implementation. The generic source theorem separately covers fields.
private def layout : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .add (by decide)).viewInput layout.affine.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.scalar.representation
      (fun value => ⟨value.val.1 + value.val.2, trivial⟩) (fun _ => rfl)
private theorem addBound : add.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem addNames : NamesBound add.program.code 3 := ⟨by decide, by decide⟩

private def sampleSpec : OracleSpec Unit := fun _ => layout.scalar.Value
private def replyView : (Σ _ : (PairSampling.input 16).Value, layout.scalar.Value) ≃ layout.scalar.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 16 sampleSpec where
  Request := (PairSampling.input 16).Value
  source _ := ()
  request := (PairSampling.input 16).representation
  reply := layout.scalar.representation.transport replyView
private def sampleSource : OracleComp sampleSpec layout.scalar.Value := queryBind () Pure.pure
private def sampler : Interactive.Code 16 := .query
private theorem sampleCorrect : Interactive.Refines port .unit (PairSampling.input 16).representation
    layout.scalar.representation (fun _ => sampleSource) sampler := by
  have projected := (Interactive.Refines.query port .unit).viewOutput layout.scalar.representation
    (fun packet => packet.2) (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem sampleTime : Interactive.TimeBound port .unit (PairSampling.input 16).representation sampler 4 :=
  Interactive.TimeBound.query
private theorem sampleWords : (sampler.lower port).descriptionWords ≤ 20 := by decide
private theorem sampleNames : WordIO.NamesBound (sampler.lower port) 3 := ⟨by decide, by decide⟩
private theorem sampleFits : (sampler.lower port).DescriptionFits :=
  WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)

private def program := CaliperBackend.SchnorrAGM.Fresh.code layout trivial add addNames.buffers (by decide) port sampler
private theorem refined : Interactive.Refines port .unit (CaliperBackend.SchnorrAGM.Cache.saved layout).representation
    (CaliperBackend.SchnorrAGM.Cache.model layout).freshOutput (CaliperBackend.SchnorrAGM.Fresh.denote layout sampleSource) program :=
  CaliperBackend.SchnorrAGM.Fresh.refines layout trivial add addNames.buffers (by decide) port sampleCorrect
private theorem time_eq : CaliperBackend.SchnorrAGM.Fresh.timeBudget layout 6 4 = 494 := by decide
private theorem words_eq : CaliperBackend.SchnorrAGM.Fresh.codeBudget layout 27 20 = 1753 := by decide
private theorem timed : Interactive.TimeBound port .unit (CaliperBackend.SchnorrAGM.Cache.saved layout).representation program 494 := by
  rw [← time_eq]
  exact CaliperBackend.SchnorrAGM.Fresh.time_bound layout trivial add addNames.buffers (by decide) port sampleCorrect addBound.time_le sampleTime
private theorem stored : (program.lower port).descriptionWords ≤ 1753 := by
  rw [← words_eq]
  exact CaliperBackend.SchnorrAGM.Fresh.code_bound layout trivial add addNames.buffers (by decide) port sampler addBound.code_le sampleWords
private theorem named : WordIO.NamesBound (program.lower port) 6 :=
  CaliperBackend.SchnorrAGM.Fresh.names layout trivial add addNames.buffers (by decide) port sampler addNames sampleNames
private theorem accepted : (program.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.Fresh.descriptionFits layout trivial add addNames.buffers (by decide) port sampler sampleFits sampleNames (by decide)

private def saved (a b : Word 16) (bad : Bool) : (CaliperBackend.SchnorrAGM.Cache.saved layout).Value :=
  ⟨((a, b), bad), ⟨trivial, trivial⟩, trivial⟩

private theorem memory (tape : RandomTape 16) (value : (CaliperBackend.SchnorrAGM.Cache.saved layout).Value) (before : State 16)
    (holds : (CaliperBackend.SchnorrAGM.Cache.saved layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute port .unit tape before)) :
    finished.time ≤ 494 ∧ ∃ answer ∈ support (CaliperBackend.SchnorrAGM.Fresh.denote layout sampleSource value),
      (CaliperBackend.SchnorrAGM.Cache.model layout).freshOutput.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (program.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((program.lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers (program.lower port).memBound) ≤
              1753 + 4 * 6 + registers + 3 * buffers + before.liveMem buffers + 494 := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    CaliperBackend.SchnorrAGM.Fresh.resources layout trivial add addNames.buffers (by decide) port sampleCorrect addBound sampleTime sampleWords
      addNames sampleNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def execute (a b : Word 16) (bad : Bool) (replies : List (Word 16)) := do
  let initial := (CaliperBackend.SchnorrAGM.Cache.saved layout).representation.initial (saved a b bad)
  let before := { initial with
    regs := fun r => if r = 200 then 99 else initial.regs r
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 10000 (program.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200,
    result.state.caps 200, result.state.regs 200, result.state.tapePos,
    (List.range 20).all (fun i => result.state.caps (i + 1) == 0), decide (result.time ≤ 494))

private def cached := CaliperBackend.SchnorrAGM.Cache.code layout trivial add addNames.buffers (by decide) port sampler
private theorem cacheRefined : Interactive.Refines port .unit (CaliperBackend.SchnorrAGM.Cache.model layout).input
    (CaliperBackend.SchnorrAGM.Cache.model layout).output (CaliperBackend.SchnorrAGM.Cache.source layout sampleSource) cached :=
  CaliperBackend.SchnorrAGM.Cache.refines layout trivial add addNames.buffers (by decide) port sampleCorrect
private theorem cacheTimed : Interactive.TimeBound port .unit (CaliperBackend.SchnorrAGM.Cache.model layout).input cached
    (CaliperBackend.SchnorrAGM.Cache.timeBudget layout 6 4) :=
  CaliperBackend.SchnorrAGM.Cache.time_bound layout trivial add addNames.buffers (by decide) port sampleCorrect addBound.time_le sampleTime
private theorem cacheStored : (cached.lower port).descriptionWords ≤ CaliperBackend.SchnorrAGM.Cache.codeBudget layout 27 20 :=
  CaliperBackend.SchnorrAGM.Cache.code_bound layout trivial add addNames.buffers (by decide) port sampler addBound.code_le sampleWords
private theorem cacheAccepted : (cached.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.Cache.descriptionFits layout trivial add addNames.buffers (by decide) port sampler
    sampleFits addNames sampleNames (by decide)

private theorem valid_iff (key : Nat × Word 16) (default : SchnorrAGM.Native.EncodedEntry (Word 16))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16))) :
    layout.cache.input.valid (key, default, entries, ()) ↔
      (key.1 < 256 ∧ entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        ((lookupValue key default entries).1 = false → entries.length ≤ 2) := by
  change (((key.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True) ∧
    (entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧ True) ∧ _) ↔ _
  simp only [and_true, true_and]
  rfl

private def empty : layout.cache.input.Value := ⟨((3, 4), (0, false, 5, 7), [], ()), by rw [valid_iff]; decide⟩
private def duplicate : layout.cache.input.Value :=
  ⟨((3, 4), (0, false, 5, 7), [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, true, 13, 14))], ()),
    by rw [valid_iff]; decide⟩
private def executeCache (request : layout.cache.input.Value) (replies : List (Word 16)) := do
  let before := (CaliperBackend.SchnorrAGM.Cache.model layout).input.initial (request, saved 5 7 false)
  let result ← WordIO.run .unit RandomTape.zero 500000 (cached.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining,
    (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ CaliperBackend.SchnorrAGM.Cache.timeBudget layout 6 4))

open Lean in
run_cmd do
  unless execute 5 7 false [9, 88] ==
      some (#[9, 1, 5, 7, 5, 7, 0], [.invoke, .input 9], [88], #[77], 4, 99, 7, true, true) do
    throwError "fresh entry lost its sampled challenge, affine explanation, framing or time bound"
  unless execute 5 7 false [65529] ==
      some (#[65529, 1, 5, 7, 5, 7, 1], [.invoke, .input 65529], [], #[77], 4, 99, 7, true, true) do
    throwError "fresh entry did not detect an exceptional challenge after modular addition"
  unless execute 11 13 true [0] ==
      some (#[0, 1, 11, 13, 11, 13, 1], [.invoke, .input 0], [], #[77], 4, 99, 7, true, true) do
    throwError "fresh entry cleared an existing bad flag or rejected a sampled zero"
  unless execute 11 0 false [0] ==
      some (#[0, 1, 11, 0, 11, 0, 1], [.invoke, .input 0], [], #[77], 4, 99, 7, true, true) do
    throwError "zero coefficient and zero challenge failed to set the bad flag"
  unless execute 11 13 false [4] ==
      some (#[4, 1, 11, 13, 11, 13, 0], [.invoke, .input 4], [], #[77], 4, 99, 7, true, true) do
    throwError "fresh entry captured constant coefficients instead of runtime state"
  unless execute 5 7 false [] == none do
    throwError "fresh entry succeeded without its scalar sampler reply"
  unless executeCache duplicate [88] ==
      some (#[2, 1, 9, 10, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14, 5, 7, 0],
        [], [88], true, true) do
    throwError "full Schnorr cache hit sampled, replaced the first explanation or changed saved state"
  unless executeCache empty [65529] ==
      some (#[65529, 1, 5, 7, 1, 3, 4, 65529, 1, 5, 7] ++ Array.replicate 12 0 ++ #[5, 7, 1],
        [.invoke, .input 65529], [], true, true) do
    throwError "Schnorr cache miss lost fresh-entry arithmetic, insertion, padding or the bad flag"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Boolean.or, ``CaliperBackend.SchnorrAGM.Fresh.arithmetic, ``CaliperBackend.SchnorrAGM.Fresh.arithmetic_time,
      ``CaliperBackend.SchnorrAGM.Fresh.arithmetic_words, ``CaliperBackend.SchnorrAGM.Fresh.arithmetic_names, ``CaliperBackend.SchnorrAGM.Fresh.refines,
      ``CaliperBackend.SchnorrAGM.Fresh.source_value, ``CaliperBackend.SchnorrAGM.Fresh.source_uniform, ``CaliperBackend.SchnorrAGM.Fresh.time_bound,
      ``CaliperBackend.SchnorrAGM.Fresh.code_bound, ``CaliperBackend.SchnorrAGM.Fresh.names, ``CaliperBackend.SchnorrAGM.Fresh.descriptionFits, ``CaliperBackend.SchnorrAGM.Fresh.resources,
      ``CaliperBackend.SchnorrAGM.Cache.refines, ``CaliperBackend.SchnorrAGM.Cache.source_value,
      ``CaliperBackend.SchnorrAGM.Cache.time_bound, ``CaliperBackend.SchnorrAGM.Cache.code_bound,
      ``CaliperBackend.SchnorrAGM.Cache.names, ``CaliperBackend.SchnorrAGM.Cache.descriptionFits,
      ``CaliperBackend.SchnorrAGM.Cache.resources,
      ``sampleCorrect, ``refined, ``timed, ``stored, ``named, ``accepted, ``memory,
      ``cacheRefined, ``cacheTimed, ``cacheStored, ``cacheAccepted] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMFresh
