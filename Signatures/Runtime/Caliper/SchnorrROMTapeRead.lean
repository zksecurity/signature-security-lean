import Signatures.Runtime.Caliper.SchnorrROMTapeReadFinish
import Signatures.Runtime.Caliper.InteractiveControlBounds
import Signatures.Runtime.Caliper.InteractiveNames
import Signatures.Runtime.Caliper.InteractiveAcceptance
import Signatures.Runtime.Caliper.InteractiveMemory

/-! Complete replay-cell query from a local fresh-cell draw. Hits execute no
draw. Misses save the scan frame, execute one draw and append its exact cell.
All retained storage is copied by the existing Caliper retain wrapper. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F I : Type} {spec : OracleSpec I} (layout : Layouts w F)

def produced {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Constructed input output f) (value : input.Value) : output.Value :=
  ⟨f value.val, body.implementation.preserves value.val value.property⟩

def drawDenote (drawSource : layout.counter.Value → OracleComp spec layout.entry.Value)
    (value : (drawInput layout).Value) : OracleComp spec (drawn layout).Value :=
  (fun fresh => (⟨(fresh.val, value.val.2), fresh.property, value.property.2⟩ : (drawn layout).Value)) <$>
    drawSource ⟨value.val.1, value.property.1⟩
def hitDenote (value : (frame layout).Value) : OracleComp spec (output layout).Value :=
  pure (produced (hit layout) value)
def missDenote (drawSource : layout.counter.Value → OracleComp spec layout.entry.Value) (value : (frame layout).Value) :
    OracleComp spec (output layout).Value :=
  drawDenote layout drawSource (produced (request layout) value) >>= fun result => pure (produced (finish layout) result)
def branchDenote (drawSource : layout.counter.Value → OracleComp spec layout.entry.Value) (value : (choice layout).Value) :
    OracleComp spec (output layout).Value :=
  Sum.elim (hitDenote layout) (missDenote layout drawSource) (sumView (frame layout) (frame layout) value)
def denote (drawSource : layout.counter.Value → OracleComp spec layout.entry.Value) (value : (input layout).Value) :
    OracleComp spec (output layout).Value :=
  branchDenote layout drawSource (produced (choose layout) value)

variable (port : Interactive.Port w spec)

def drawCode (draw : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain draw (Interactive.savedBuffer port draw) layout.counter.representation.encoding.words
    layout.entry.representation.encoding.words (frame layout).representation.encoding.words
def missCode (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (request layout).implementation.program.code)
    (.seq (drawCode layout port draw) (.compute (finish layout).implementation.program.code))
def branchCode (draw : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (.compute (hit layout).implementation.program.code) (missCode layout port draw)
    (frame layout).representation.encoding.words (frame layout).representation.encoding.words
def code (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (choose layout).implementation.program.code) (branchCode layout port draw)

variable {layout port}
    {drawSource : layout.counter.Value → OracleComp spec layout.entry.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw)

include drawCorrect in
theorem draw_refines : Interactive.Refines port .unit (drawInput layout).representation (drawn layout).representation
    (drawDenote layout drawSource) (drawCode layout port draw) := by
  have retained := drawCorrect.retain (by decide) (frame layout).representation layout.wordFits
    (drawInput layout).representation.fits (drawn layout).representation.fits
  have viewed := (retained.viewInput (drawInput layout).representation (productView layout.counter (frame layout)) (fun _ => rfl)).viewOutput
    (drawn layout).representation (productView layout.entry (frame layout)).symm (by
      intro value
      exact congrArg (layout.entry.representation.prod (frame layout).representation (drawn layout).representation.fits).encoding.encode
        ((productView layout.entry (frame layout)).apply_symm_apply value))
  convert viewed using 1
  · funext value
    exact PFunctor.FreeM.comp_map (productView layout.entry (frame layout)).symm
      (fun fresh => (fresh, ⟨value.val.2, value.property.2⟩)) (drawSource ⟨value.val.1, value.property.1⟩)
  · rfl

include drawCorrect in
theorem miss_refines : Interactive.Refines port .unit (frame layout).representation (output layout).representation
    (missDenote layout drawSource) (missCode layout port draw) := by
  convert (Interactive.Refines.compute port .unit (request layout).implementation.program).seq
    ((draw_refines drawCorrect).seq (Interactive.Refines.compute port .unit (finish layout).implementation.program)) using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

include drawCorrect in
theorem branch_refines : Interactive.Refines port .unit (choice layout).representation (output layout).representation
    (branchDenote layout drawSource) (branchCode layout port draw) :=
  (Interactive.Refines.dispatch (frame layout).representation (frame layout).representation (output layout).representation
    (Interactive.Refines.compute port .unit (hit layout).implementation.program) (miss_refines drawCorrect) (width_pos layout.wordFits)
    (choice layout).representation.fits).viewInput (choice layout).representation (sumView (frame layout) (frame layout)) (fun _ => rfl)

include drawCorrect in
theorem refines : Interactive.Refines port .unit (input layout).representation (output layout).representation
    (denote layout drawSource) (code layout port draw) := by
  convert (Interactive.Refines.compute port .unit (choose layout).implementation.program).seq (branch_refines drawCorrect) using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

variable (layout)

theorem denote_value (drawSource : layout.counter.Value → OracleComp spec layout.entry.Value) (value : (input layout).Value) :
    Subtype.val <$> denote layout drawSource value =
      let scan := Schnorr.SeedTape.pop value.val.1 value.val.2.1 value.val.2.2.2
      if scan.1 then pure (scan.2.1, value.val.2.2.1, scan.2.2)
      else (fun fresh => (fresh.val, value.val.2.2.1 ++ [fresh.val], scan.2.2)) <$>
        drawSource ⟨value.val.1, value.property.1⟩ := by
  cases found : (Schnorr.SeedTape.pop value.val.1 value.val.2.1 value.val.2.2.2).1 <;>
    simp [denote, branchDenote, produced, Boolean.select, sumView, hitDenote,
      missDenote, drawDenote, found, bind_pure_comp, Functor.map_map]

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
