import Proofs.Runtime.Caliper.BLSReplyBounds

/-! A stored request tag selects the actual BLS hashing or signing reply program.
The dispatcher executes tag loading, branching and payload normalization. Its
input carries exactly the selected handler's domain invariant. -/

namespace Signatures.Runtime.CaliperBackend.BLSDispatch
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {M R C G : Type} [DecidableEq M] (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value)

def input : Layout w (BLSReply.Input M R C G ⊕ BLSReply.Input M R C G) :=
  (layout.input default.val false).sum (layout.input default.val true) (width_pos layout.cache.wordFits) (by
    have left := layout.input_le default.val false
    have right := layout.input_le default.val true
    have storage := layout.storageFits
    have width := layout.cache.wordFits
    change 16 * layout.width < 2 ^ w at storage
    omega)

def request (signing : Bool) (value : (layout.input default.val signing).Value) : (input layout default).Value :=
  match signing with
  | false => ⟨.inl value.val, value.property⟩
  | true => ⟨.inr value.val, value.property⟩

variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

def code : Interactive.Code w :=
  Interactive.dispatch
    (BLSReply.code layout default false P comparison correct port draw (response false) (responseBuffers false) reserve)
    (BLSReply.code layout default true P comparison correct port draw (response true) (responseBuffers true) reserve)
    (layout.input default.val false).representation.encoding.words (layout.input default.val true).representation.encoding.words

def denote (drawSource : ProbComp layout.cache.value.Value) (value : (input layout default).Value) : ProbComp layout.output.Value :=
  Sum.elim (BLSReply.denote layout default false P comparison correct (response false) (responseBuffers false) reserve drawSource)
    (BLSReply.denote layout default true P comparison correct (response true) (responseBuffers true) reserve drawSource)
    (sumView (layout.input default.val false) (layout.input default.val true) value)

theorem refines (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw) :
    Interactive.Refines port .unit (input layout default).representation layout.output.representation
      (denote layout default P comparison correct response responseBuffers reserve drawSource)
      (code layout default P comparison correct port draw response responseBuffers reserve) :=
  (Interactive.Refines.dispatch (layout.input default.val false).representation (layout.input default.val true).representation
    layout.output.representation
    (BLSReply.refines layout default false P comparison correct port draw (response false) (responseBuffers false) reserve drawSource drawCorrect)
    (BLSReply.refines layout default true P comparison correct port draw (response true) (responseBuffers true) reserve drawSource drawCorrect)
    (width_pos layout.cache.wordFits) (input layout default).representation.fits).viewInput (input layout default).representation
      (sumView (layout.input default.val false) (layout.input default.val true)) (fun _ => rfl)

theorem denote_request (drawSource : ProbComp layout.cache.value.Value) (signing : Bool) (value : (layout.input default.val signing).Value) :
    denote layout default P comparison correct response responseBuffers reserve drawSource (request layout default signing value) =
      BLSReply.denote layout default signing P comparison correct (response signing) (responseBuffers signing) reserve drawSource value := by
  cases signing <;> rfl

variable {drawSource : ProbComp layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw)
    {drawTime drawWords : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    {responseTime responseWords : Bool → Nat}
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))

def timeBudget (drawTime : Nat) (responseTime : Bool → Nat) : Nat :=
  max (BLSReply.timeBudget layout drawTime (responseTime false)) (BLSReply.timeBudget layout drawTime (responseTime true)) + 8 * layout.width + 2

def codeBudget (drawWords : Nat) (responseWords : Bool → Nat) : Nat :=
  BLSReply.codeBudget layout drawWords (responseWords false) + BLSReply.codeBudget layout drawWords (responseWords true) + 52 * layout.width + 40

include drawCorrect drawTimeBound responseBound in
theorem time_bound : Interactive.TimeBound port .unit (input layout default).representation
    (code layout default P comparison correct port draw response responseBuffers reserve) (timeBudget layout drawTime responseTime) := by
  have dispatched := Interactive.TimeBound.dispatch (layout.input default.val false).representation (layout.input default.val true).representation
    (BLSReply.time_bound layout default false P comparison correct port draw drawCorrect drawTimeBound (response false) (responseBuffers false) reserve (responseBound false))
    (BLSReply.time_bound layout default true P comparison correct port draw drawCorrect drawTimeBound (response true) (responseBuffers true) reserve (responseBound true))
    (width_pos layout.cache.wordFits) (input layout default).representation.fits
  apply (dispatched.viewInput (input layout default).representation (sumView (layout.input default.val false) (layout.input default.val true)) (fun _ => rfl)).mono
  rw [Interactive.dispatchTime_unit]
  have left := layout.input_le default.val false
  have right := layout.input_le default.val true
  dsimp only [timeBudget]
  omega

include drawWordsBound responseBound in
theorem code_bound : ((code layout default P comparison correct port draw response responseBuffers reserve).lower port).descriptionWords ≤
    codeBudget layout drawWords responseWords := by
  have left := BLSReply.code_bound layout default false P comparison correct port draw drawWordsBound (response false) (responseBuffers false) reserve (responseBound false)
  have right := BLSReply.code_bound layout default true P comparison correct port draw drawWordsBound (response true) (responseBuffers true) reserve (responseBound true)
  have leftWidth := layout.input_le default.val false
  have rightWidth := layout.input_le default.val true
  rw [code, Interactive.dispatch_descriptionWords]
  dsimp only [codeBudget]
  omega

theorem names {drawSlots responseSlots : Nat} (drawNames : WordIO.NamesBound (draw.lower port) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots) :
    WordIO.NamesAccounted ((code layout default P comparison correct port draw response responseBuffers reserve).lower port)
      (max (max 5 drawSlots) responseSlots) :=
  Interactive.dispatch_names port
    (BLSReply.names layout default false P comparison correct port draw (response false) (responseBuffers false) reserve drawNames (responseNames false))
    (BLSReply.names layout default true P comparison correct port draw (response true) (responseBuffers true) reserve drawNames (responseNames true)) _ _

theorem descriptionFits {drawSlots : Nat} (drawFits : (draw.lower port).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 1 < 2 ^ w) :
    ((code layout default P comparison correct port draw response responseBuffers reserve).lower port).DescriptionFits :=
  Interactive.dispatch_descriptionFits port _ _ _ _ layout.cache.wordFits
    (BLSReply.descriptionFits layout default false P comparison correct port draw (response false) (responseBuffers false) reserve drawFits drawNames drawReserve)
    (BLSReply.descriptionFits layout default true P comparison correct port draw (response true) (responseBuffers true) reserve drawFits drawNames drawReserve)
    (layout.input default.val false).representation.fits (layout.input default.val true).representation.fits

end Signatures.Runtime.CaliperBackend.BLSDispatch
