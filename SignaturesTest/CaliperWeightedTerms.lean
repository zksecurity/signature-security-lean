import Signatures.Runtime.Caliper.OOPSTermsBounds
import Lean

/-! Execute both weighted generators on actual word buffers. Field source
identities are proved generically; word multiplication tests the implementation
wiring, framing, zero dimensions and modular arithmetic. -/
namespace SignaturesTest.CaliperWeightedTerms
open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

private def scalar : Layout 16 (Word 16) := Layout.all (wordRepresentation 16 (by decide))
private def pair := scalar.prod scalar (by decide)
private def mul : Implementation .unit pair scalar (fun value => value.1 * value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput pair.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput scalar.representation
      (fun value => ⟨value.val.1 * value.val.2, trivial⟩) (fun _ => rfl)
private theorem mulBound : mul.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem mulNames : NamesBound mul.program.code 3 := ⟨by decide, by decide⟩

private def proximity : ProximityTerms.Layouts 16 (Word 16) (Word 16) 2 :=
  ⟨scalar, scalar, by decide, by decide, by decide⟩
private def proximityZero : ProximityTerms.Layouts 16 (Word 16) (Word 16) 0 :=
  ⟨scalar, scalar, by decide, by decide, by decide⟩
private def oops : OOPSTerms.Layouts 16 (Word 16) (Word 16) 3 :=
  ⟨scalar, scalar, by decide, by decide, by decide⟩
private def oopsZero : OOPSTerms.Layouts 16 (Word 16) (Word 16) 0 :=
  ⟨scalar, scalar, by decide, by decide, by decide⟩

private def proximityProgram := ProximityTerms.implementation proximity trivial
private def proximityZeroProgram := ProximityTerms.implementation proximityZero trivial
private def oopsProgram := OOPSTerms.implementation oops trivial mul mulNames.buffers (by decide)
private def oopsZeroProgram := OOPSTerms.implementation oopsZero trivial mul mulNames.buffers (by decide)

private theorem oopsBound : oopsProgram.BoundedBy (OOPSTerms.timeBudget oops 6) (OOPSTerms.codeBudget oops 27) :=
  OOPSTerms.bounded oops trivial mul mulNames.buffers (by decide) mulBound
private theorem oopsNamed : NamesAccounted oopsProgram.program.code 3 :=
  OOPSTerms.names oops trivial mul mulNames.buffers (by decide) mulNames.accounted

private def execute {A B : Type} {input : Layout 16 A} {output : Layout 16 B} {f : A → B}
    (program : Implementation .unit input output f) (value : input.Value) (time : Nat) :=
  let initial := input.representation.initial value
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 1000000 program.program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 30).all (fun i => result.1.caps (i + 1) == 0), decide (result.2.1 ≤ time))

private def vectorInput (a b topic : Word 16) : proximity.input.Value :=
  ⟨((fun i => if i.val = 0 then a else b), topic), (fun _ => trivial), trivial⟩
private def oopsInput (message topic : Word 16) : oops.input.Value := ⟨(message, topic), trivial, trivial⟩

private instance : One Unit := ⟨()⟩
private def emptyWidths : ProximityTerms.Layouts 16 Unit Unit 2 :=
  ⟨DataImplementation.unitLayout 16, DataImplementation.unitLayout 16, by decide, by decide, by decide⟩
private def emptyWidthsProgram := ProximityTerms.implementation emptyWidths trivial

private def restricted : ProximityTerms.Layouts 16 Nat (Word 16) 2 :=
  ⟨Layout.counter 16 4 (by decide) (by decide), scalar, by decide, by decide, by decide⟩
example : ¬ restricted.input.valid ((fun _ => 5), 42) := by
  intro valid
  have bound := valid.1 0
  change 5 < 4 at bound
  omega

example (input : proximity.input.Value) :
    proximity.input.representation.encoding.decode (proximity.input.representation.encoding.encode input) = some input :=
  proximity.input.representation.encoding.decode_encode input

private theorem oopsMemory (tape : RandomTape 16) (value : oops.input.Value) (before : State 16)
    (holds : oops.input.representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape oopsProgram.program.code before after
      (oopsProgram.program.time value) net peak ∧
      oops.output.representation.Holds ⟨OOPSTerms.value value.val, oopsProgram.preserves value.val value.property⟩ after ∧
      oopsProgram.program.time value ≤ OOPSTerms.timeBudget oops 6 ∧
      ∀ between, (Caliper.Reaches .unit tape oopsProgram.program.code before between ∨ between = after) →
        (staticWords oopsProgram.program.code registers buffers : Int) +
          between.liveMem (max buffers oopsProgram.program.code.memBound) ≤
            5 * OOPSTerms.codeBudget oops 27 + 12 + registers + 3 * buffers +
              before.liveMem buffers + OOPSTerms.timeBudget oops 6 :=
  OOPSTerms.resources oops trivial mul mulNames.buffers (by decide) mulBound mulNames.accounted
    tape value before holds registers buffers initialRegisters initialBuffers

open Lean in
run_cmd do
  unless execute proximityProgram (vectorInput 5 7 42) (ProximityTerms.timeBudget proximity) ==
      some (#[3, 0, 42, 1, 1, 42, 5, 2, 42, 7], #[77], 4, 91, 9, true, true) do
    throwError "Proximity lost the constant, coordinate order, repeated slot, framing or time bound"
  unless execute proximityProgram (vectorInput 0 65535 99) (ProximityTerms.timeBudget proximity) ==
      some (#[3, 0, 99, 1, 1, 99, 0, 2, 99, 65535], #[77], 4, 91, 9, true, true) do
    throwError "Proximity dropped zero weights or changed runtime coordinate/slot bytes"
  unless execute proximityZeroProgram ⟨(Fin.elim0, 42), (fun i => Fin.elim0 i), trivial⟩
      (ProximityTerms.timeBudget proximityZero) ==
      some (#[1, 0, 42, 1], #[77], 4, 91, 9, true, true) do
    throwError "dimension-zero Proximity omitted its constant weighted base"
  unless execute emptyWidthsProgram ⟨((fun _ => ()), ()), (fun _ => trivial), trivial⟩
      (ProximityTerms.timeBudget emptyWidths) ==
      some (#[3, 0, 1, 2], #[77], 4, 91, 9, true, true) do
    throwError "zero-word scalar/slot encodings caused invalid reads or missing tags"
  unless execute oopsProgram (oopsInput 3 42) (OOPSTerms.timeBudget oops 6) ==
      some (#[4, 0, 42, 1, 1, 42, 3, 2, 42, 9, 3, 42, 27], #[77], 4, 91, 9, true, true) do
    throwError "OOPS lost successive powers, finite degree tags, topic retention or its time bound"
  unless execute oopsProgram (oopsInput 65535 7) (OOPSTerms.timeBudget oops 6) ==
      some (#[4, 0, 7, 1, 1, 7, 65535, 2, 7, 1, 3, 7, 65535], #[77], 4, 91, 9, true, true) do
    throwError "OOPS bypassed the supplied modular multiplication routine"
  unless execute oopsZeroProgram ⟨(123, 42), trivial, trivial⟩ (OOPSTerms.timeBudget oopsZero 6) ==
      some (#[1, 0, 42, 1], #[77], 4, 91, 9, true, true) do
    throwError "degree-zero OOPS depended on a positive-degree term"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``vectorEncoding_words, ``vectorEncoding_read, ``boundedList_encode_ofFn,
      ``ProximityTerms.implementation, ``ProximityTerms.source, ``ProximityTerms.bounded,
      ``ProximityTerms.resources, ``Powers.compile, ``Powers.bounded, ``Powers.names,
      ``Powers.values_eq, ``OOPSTerms.implementation, ``OOPSTerms.source,
      ``OOPSTerms.bounded, ``OOPSTerms.names, ``OOPSTerms.resources, ``oopsBound, ``oopsNamed, ``oopsMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

open Lean Meta in
run_meta do
  for (name, expected) in #[( ``ProximityTerms.implementation, 0), (``OOPSTerms.implementation, 1)] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      let mut implementations := 0
      for param in params do
        let premise ← inferType param
        if premise.getAppFn.isConstOf ``Implementation then
          implementations := implementations + 1
      unless implementations == expected do
        throwError "{name}: generator must derive all code except its named scalar multiplication"

end SignaturesTest.CaliperWeightedTerms
