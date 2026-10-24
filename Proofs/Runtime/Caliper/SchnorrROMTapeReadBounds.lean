import Proofs.Runtime.Caliper.SchnorrROMTapeRead

/-! Derived bounds for the replay handler. Only the fresh-cell primitive has
an external budget; scanning, dispatch, saved frames and append are charged. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F I : Type} {spec : OracleSpec I}
    (layout : Layouts w F) (port : Interactive.Port w spec)
    {drawSource : layout.counter.Value → OracleComp spec layout.entry.Value} {draw : Interactive.Code w}

def drawOverhead : Nat :=
  8 * layout.counter.representation.encoding.words + 8 * layout.entry.representation.encoding.words +
    12 * (frame layout).representation.encoding.words
def branchTime (drawTime : Nat) : Nat :=
  (hit layout).budget.time + (request layout).budget.time + (finish layout).budget.time +
    drawTime + drawOverhead layout + 8 * (frame layout).representation.encoding.words + 2
def timeBudget (drawTime : Nat) : Nat := (choose layout).budget.time + branchTime layout drawTime
def codeBudget (drawWords : Nat) : Nat :=
  (choose layout).budget.words + (hit layout).budget.words + (request layout).budget.words +
    (finish layout).budget.words + drawWords + 26 * layout.counter.representation.encoding.words +
    26 * layout.entry.representation.encoding.words + 91 * (frame layout).representation.encoding.words + 100

theorem draw_time
    (drawCorrect : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw)
    {drawTime : Nat} (drawBound : Interactive.TimeBound port .unit layout.counter.representation draw drawTime) :
    Interactive.TimeBound port .unit (drawInput layout).representation (drawCode layout port draw)
      (drawTime + drawOverhead layout) := by
  have retained := drawBound.retain drawCorrect (by decide) (frame layout).representation layout.wordFits
    (drawInput layout).representation.fits
  have viewed := retained.viewInput (drawInput layout).representation
    (productView layout.counter (frame layout)) (fun _ => rfl)
  apply viewed.mono
  have bound := Interactive.retain_time_unit_le (w := w) (Interactive.savedBuffer port draw)
    layout.counter.representation.encoding.words layout.entry.representation.encoding.words
    (frame layout).representation.encoding.words drawTime
  simpa only [drawOverhead, Nat.add_assoc, WordIO.Costs.unit] using bound

theorem miss_time
    (drawCorrect : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw)
    {drawTime : Nat} (drawBound : Interactive.TimeBound port .unit layout.counter.representation draw drawTime) :
    Interactive.TimeBound port .unit (frame layout).representation (missCode layout port draw)
      ((request layout).budget.time + (drawTime + drawOverhead layout + (finish layout).budget.time)) :=
  (Interactive.TimeBound.compute (port := port) (cost := .unit) (request layout).implementation.program _
    (request layout).bounded.time_le).seq (Interactive.Refines.compute port .unit (request layout).implementation.program)
      ((draw_time layout port drawCorrect drawBound).seq (draw_refines drawCorrect)
        (Interactive.TimeBound.compute (port := port) (cost := .unit) (finish layout).implementation.program _
          (finish layout).bounded.time_le))

theorem branch_time
    (drawCorrect : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw)
    {drawTime : Nat} (drawBound : Interactive.TimeBound port .unit layout.counter.representation draw drawTime) :
    Interactive.TimeBound port .unit (choice layout).representation (branchCode layout port draw)
      (branchTime layout drawTime) := by
  have hitBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (hit layout).implementation.program _
    (hit layout).bounded.time_le
  have dispatched := hitBound.dispatch (frame layout).representation (frame layout).representation
    (miss_time layout port drawCorrect drawBound) (width_pos layout.wordFits) (choice layout).representation.fits
  have viewed := dispatched.viewInput (choice layout).representation (sumView (frame layout) (frame layout)) (fun _ => rfl)
  apply viewed.mono
  rw [Interactive.dispatchTime_unit]
  unfold branchTime
  omega

theorem time_bound
    (drawCorrect : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw)
    {drawTime : Nat} (drawBound : Interactive.TimeBound port .unit layout.counter.representation draw drawTime) :
    Interactive.TimeBound port .unit (input layout).representation (code layout port draw) (timeBudget layout drawTime) :=
  (Interactive.TimeBound.compute (port := port) (cost := .unit) (choose layout).implementation.program _
    (choose layout).bounded.time_le).seq (Interactive.Refines.compute port .unit (choose layout).implementation.program)
      (branch_time layout port drawCorrect drawBound)

theorem draw_words (draw : Interactive.Code w) :
    ((drawCode layout port draw).lower port).descriptionWords ≤ (draw.lower port).descriptionWords +
      26 * layout.counter.representation.encoding.words + 26 * layout.entry.representation.encoding.words +
      39 * (frame layout).representation.encoding.words + 41 :=
  Interactive.retain_descriptionWords_le port draw (Interactive.savedBuffer port draw) _ _ _

theorem miss_words (draw : Interactive.Code w) :
    ((missCode layout port draw).lower port).descriptionWords ≤ (draw.lower port).descriptionWords +
      (request layout).budget.words + (finish layout).budget.words +
      26 * layout.counter.representation.encoding.words + 26 * layout.entry.representation.encoding.words +
      39 * (frame layout).representation.encoding.words + 45 := by
  have retained := draw_words layout port draw
  have requested := (request layout).bounded.code_le
  have finished := (finish layout).bounded.code_le
  simp only [missCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem code_bound (draw : Interactive.Code w) {drawWords : Nat}
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((code layout port draw).lower port).descriptionWords ≤ codeBudget layout drawWords := by
  have chosen := (choose layout).bounded.code_le
  have hitBound := (hit layout).bounded.code_le
  have missBound := miss_words layout port draw
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq]
  rw [show (branchCode layout port draw).lower port =
    (Interactive.dispatch (.compute (hit layout).implementation.program.code) (missCode layout port draw)
      (frame layout).representation.encoding.words (frame layout).representation.encoding.words).lower port from rfl]
  rw [Interactive.dispatch_descriptionWords]
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
