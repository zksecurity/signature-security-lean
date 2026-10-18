import Signatures.Runtime.Caliper.SourceMemory
import Signatures.Runtime.Caliper.InteractiveAcceptance
import Signatures.Runtime.Caliper.CapacityBounds

/-! Checked emission of compiled reduction programs. Existing primitive proofs
and layout bounds discharge all word-width conditions except newly reserved
caller buffers. A structural check verifies those names before emission.
-/

namespace Signatures.Runtime.CaliperBackend.SourceCompilation

open Caliper OracleComp OracleSpec PFunctor BoundedSource

universe v u

variable {w : Nat} {I : Type} {spec : OracleSpec I}
    {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
    {Q : QuantitativeStepClass.{0, v, u} C} {sourceIface : BackendProgram.Interface (C := C) spec}
    {targetIface : Interface w spec} {cost : WordIO.Costs} {hw : 16 < 2 ^ w}

/-- This check is deliberately conservative: even a bounded loop with zero
iterations checks its body. It introduces no unchecked executable operation. -/
def Compilation.checkNames {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B} :
    Compilation targetIface cost hw source input output → Bool
  | .atomic _ _ | .query => true
  | .seq initial following | .branch initial following _ => initial.checkNames && following.checkNames
  | .first _ _ body _ _ => body.checkNames && decide (Interactive.savedBuffer targetIface.port body.compile < 2 ^ w)
  | .loop _ body stop _ => body.checkNames && stop.checkNames
  | .iterate _ body _ _ _ => body.checkNames && decide (Interactive.savedBuffer targetIface.port body.compile < 2 ^ w)

theorem Compilation.descriptionFits {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) (accepted : code.checkNames = true) :
    (code.compile.lower targetIface.port).DescriptionFits := by
  induction code with
  | atomic source implementation => exact .compute implementation.program.description_fits
  | query => exact WordIO.exchange_descriptionFits _ _ hw targetIface.reply.fits
  | seq first second ih₁ ih₂ =>
    have accepted : first.checkNames = true ∧ second.checkNames = true := by simpa [checkNames] using accepted
    obtain ⟨left, right⟩ := accepted
    exact WordIO.Code.DescriptionFits.seq hw (ih₁ left) (ih₂ right)
  | @branch A B D a b d left right leftInput rightInput output first second fits ih₁ ih₂ =>
    have accepted : first.checkNames = true ∧ second.checkNames = true := by simpa [checkNames] using accepted
    obtain ⟨left, right⟩ := accepted
    exact Interactive.dispatch_descriptionFits targetIface.port _ _ _ _ hw (ih₁ left) (ih₂ right)
      leftInput.representation.fits rightInput.representation.fits
  | @first A B S a b s body input output saved code inputFits outputFits ih =>
    have accepted : code.checkNames = true ∧ Interactive.savedBuffer targetIface.port code.compile < 2 ^ w := by
      simpa [checkNames] using accepted
    obtain ⟨bodyAccepted, name⟩ := accepted
    exact Interactive.retain_descriptionFits targetIface.port _ _ _ _ _ hw (ih bodyAccepted)
      name input.representation.fits saved.representation.fits outputFits
  | @loop S B s b body stop state result fits step finish fuel ihBody ihStop =>
    have accepted : step.checkNames = true ∧ finish.checkNames = true := by simpa [checkNames] using accepted
    obtain ⟨bodyAccepted, stopAccepted⟩ := accepted
    exact Interactive.loop_descriptionFits targetIface.port _ _ _ _ fuel hw (ihBody bodyAccepted) (ihStop stopAccepted)
      result.representation.fits state.representation.fits
  | @iterate S s counter body state code fuel counterFits storageFits ih =>
    have accepted : code.checkNames = true ∧ Interactive.savedBuffer targetIface.port code.compile < 2 ^ w := by
      simpa [checkNames] using accepted
    exact Interactive.Counted.descriptionFits targetIface.port _ _ _ fuel hw (ih accepted.1) accepted.2 storageFits

/-- Emit only accepted code, with a proof that every stored operand fits. The
emitted program is exactly the one used by refinement and resource theorems. -/
def Compilation.emit {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) : Option {program : WordIO.Code w // program.DescriptionFits} :=
  if accepted : code.checkNames = true then some ⟨code.compile.lower targetIface.port, code.descriptionFits accepted⟩ else none

theorem Compilation.emit_eq {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) :
    Subtype.val <$> code.emit = if code.checkNames then some (code.compile.lower targetIface.port) else none := by
  unfold emit
  split_ifs <;> rfl

theorem Compilation.descriptorsFit {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) (accepted : code.checkNames = true)
    {tape : RandomTape w} {before after between : State w} {trace : List (WordIO.Event w)}
    {time : Nat} {net peak : Int} {value : input.Value}
    (represented : input.representation.Holds value before)
    {execution : WordIO.Exec cost tape (code.compile.lower targetIface.port) before after trace time net peak}
    (visited : execution.Visits between) :
    ∀ buffer, (between.bufs buffer).size ≤ between.caps buffer ∧ between.caps buffer < 2 ^ w :=
  visited.descriptorsFit (code.descriptionFits accepted) represented.2.2.2 represented.2.2.1

end Signatures.Runtime.CaliperBackend.SourceCompilation
