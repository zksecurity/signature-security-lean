import Proofs.Runtime.Caliper.SchnorrAGMHandlerSource
import Proofs.Runtime.Caliper.SumContextMerge
import Proofs.Runtime.Caliper.ReorderTail

/-! Independent caller request/reply packets and the reduction's private store.
All distribution of tags/padding and movement of the store executes word copies.
The admission proof only packages bytes already constructed by preparation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerPackets
open Caliper BoundedSource
variable {w qH qS randomBound : Nat} {M F G : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)

def width : Nat := 3 + layout.randomArgs.representation.encoding.words + layout.groupArgs.representation.encoding.words +
  layout.random.reply.representation.encoding.words + layout.signing.reply.representation.encoding.words +
    layout.scheme.store.representation.encoding.words
theorem width_fits : width layout < 2 ^ w := by
  have random := Handler.Dispatch.random_output_le layout
  have scalar := layout.scalarOutput_le
  change layout.random.reply.representation.encoding.words + layout.scheme.store.representation.encoding.words ≤ _ at random
  change layout.signing.reply.representation.encoding.words + layout.scheme.store.representation.encoding.words ≤ _ at scalar
  have := layout.args_le; have := layout.width_pos
  apply layout.fits_of_le
  unfold width
  omega
theorem fits {words : Nat} (bound : words ≤ width layout) : words < 2 ^ w := bound.trans_lt (width_fits layout)

abbrev Request := layout.randomArgs.Value ⊕ (layout.groupArgs.Value ⊕ layout.groupArgs.Value)
abbrev Packet := Request layout × layout.scheme.store.Value
abbrev Raw := (layout.randomArgs.Value × layout.scheme.store.Value) ⊕
  ((layout.groupArgs.Value × layout.scheme.store.Value) ⊕ (layout.groupArgs.Value × layout.scheme.store.Value))

abbrev groupRequest := layout.groupArgs.representation.sum layout.groupArgs.representation (width_pos layout.scheme.wordFits)
  (fits layout (by unfold width; omega))
abbrev request : Representation w (Request layout) := layout.randomArgs.representation.sum (groupRequest layout)
  (width_pos layout.scheme.wordFits) (fits layout (by change 1 + max _ (1 + max _ _) ≤ _; unfold width; omega))
abbrev input : Representation w (Packet layout) := (request layout).prod layout.scheme.store.representation
  (fits layout (by change 1 + max _ (1 + max _ _) + _ ≤ _; unfold width; omega))
abbrev randomInput := layout.randomArgs.representation.prod layout.scheme.store.representation
  (fits layout (by unfold width; omega))
abbrev groupInput := (groupRequest layout).prod layout.scheme.store.representation
  (fits layout (by change 1 + max _ _ + _ ≤ _; unfold width; omega))
abbrev groupRaw := SumContext.output layout.groupArgs.representation layout.groupArgs.representation
  layout.scheme.store.representation layout.scheme.wordFits (groupInput layout).fits
abbrev raw : Representation w (Raw layout) := (randomInput layout).sum (groupRaw layout) (width_pos layout.scheme.wordFits)
  (fits layout (by change 1 + max (_ + _) (1 + max (_ + _) (_ + _)) ≤ _; unfold width; omega))

def prepared (value : Packet layout) : Raw layout :=
  match value.1 with
  | .inl args => .inl (args, value.2)
  | .inr (.inl args) => .inr (.inl (args, value.2))
  | .inr (.inr args) => .inr (.inr (args, value.2))

def prepare : Realizer .unit (input layout) (raw layout) (prepared layout) :=
  ((SumContext.distribute layout.randomArgs.representation (groupRequest layout) layout.scheme.store.representation
    layout.scheme.wordFits (input layout).fits).then
      (branchRealizer .unit (by decide) (randomInput layout) (groupInput layout) (raw layout)
        (inlRealizer .unit (by decide) (randomInput layout) (groupRaw layout) layout.scheme.wordFits (raw layout).fits)
        ((SumContext.distribute layout.groupArgs.representation layout.groupArgs.representation layout.scheme.store.representation
          layout.scheme.wordFits (groupInput layout).fits).then
            (inrRealizer .unit (by decide) (randomInput layout) (groupRaw layout) layout.scheme.wordFits (raw layout).fits))
        layout.scheme.wordFits (fits layout (by change 1 + max (_ + _) ((1 + max _ _) + _) ≤ _; unfold width; omega)))).viewOutput
          (raw layout) (prepared layout) (by intro value; rcases value with ⟨args | (args | args), saved⟩ <;> rfl)

abbrev RandomReply := layout.random.reply.Value × layout.randomArgs.Value
abbrev GroupReply := layout.signing.reply.Value × layout.groupArgs.Value
abbrev Reply := RandomReply layout ⊕ (GroupReply layout ⊕ GroupReply layout)
abbrev randomReply := layout.random.reply.representation.prod layout.randomArgs.representation
  (fits layout (by unfold width; omega))
abbrev groupReply := layout.signing.reply.representation.prod layout.groupArgs.representation
  (fits layout (by unfold width; omega))
abbrev groupReplies := (groupReply layout).sum (groupReply layout) (width_pos layout.scheme.wordFits)
  (fits layout (by change 1 + max (_ + _) (_ + _) ≤ _; unfold width; omega))
abbrev reply : Representation w (Reply layout) := (randomReply layout).sum (groupReplies layout) (width_pos layout.scheme.wordFits)
  (fits layout (by change 1 + max (_ + _) (1 + max (_ + _) (_ + _)) ≤ _; unfold width; omega))
abbrev output : Representation w (Reply layout × layout.scheme.store.Value) := (reply layout).prod layout.scheme.store.representation
  (fits layout (by change 1 + max (_ + _) (1 + max (_ + _) (_ + _)) + _ ≤ _; unfold width; omega))
abbrev randomFinished := (randomReply layout).prod layout.scheme.store.representation
  (fits layout (by change (_ + _) + _ ≤ _; unfold width; omega))
abbrev groupFinished := (groupReply layout).prod layout.scheme.store.representation
  (fits layout (by change (_ + _) + _ ≤ _; unfold width; omega))
abbrev groupsFinished := (groupReplies layout).prod layout.scheme.store.representation
  (fits layout (by change 1 + max (_ + _) (_ + _) + _ ≤ _; unfold width; omega))

def randomFinishValue (value : layout.randomOutput.Value × layout.randomArgs.Value) : RandomReply layout × layout.scheme.store.Value :=
  let pair := productView layout.random.reply layout.scheme.store value.1
  ((pair.1, value.2), pair.2)
def groupFinishValue (value : layout.scalarOutput.Value × layout.groupArgs.Value) : GroupReply layout × layout.scheme.store.Value :=
  let pair := productView layout.signing.reply layout.scheme.store value.1
  ((pair.1, value.2), pair.2)

def randomFinish : Realizer .unit (Handler.Dispatch.randomPacket layout) (randomFinished layout) (randomFinishValue layout) :=
  ((ReorderTail.realizer layout.random.reply.representation layout.scheme.store.representation layout.randomArgs.representation
    layout.scheme.wordFits (Handler.Dispatch.randomPacket layout).fits).viewInput (Handler.Dispatch.randomPacket layout)
      (fun value => (productView layout.random.reply layout.scheme.store value.1, value.2)) (fun _ => rfl)).viewOutput
        (randomFinished layout) (randomFinishValue layout) (fun _ => rfl)
def groupFinish : Realizer .unit (Handler.Dispatch.groupPacket layout) (groupFinished layout) (groupFinishValue layout) :=
  ((ReorderTail.realizer layout.signing.reply.representation layout.scheme.store.representation layout.groupArgs.representation
    layout.scheme.wordFits (Handler.Dispatch.groupPacket layout).fits).viewInput (Handler.Dispatch.groupPacket layout)
      (fun value => (productView layout.signing.reply layout.scheme.store value.1, value.2)) (fun _ => rfl)).viewOutput
        (groupFinished layout) (groupFinishValue layout) (fun _ => rfl)

def groupsFinishValue : (layout.scalarOutput.Value × layout.groupArgs.Value) ⊕ (layout.scalarOutput.Value × layout.groupArgs.Value) →
    (GroupReply layout ⊕ GroupReply layout) × layout.scheme.store.Value
  | .inl value => (.inl (groupFinishValue layout value).1, (groupFinishValue layout value).2)
  | .inr value => (.inr (groupFinishValue layout value).1, (groupFinishValue layout value).2)
def groupsFinish : Realizer .unit (Handler.Dispatch.groupOutput layout) (groupsFinished layout) (groupsFinishValue layout) :=
  (branchRealizer .unit (by decide) (Handler.Dispatch.groupPacket layout) (Handler.Dispatch.groupPacket layout) (groupsFinished layout)
    ((groupFinish layout).then (SumContext.mergeLeft (groupReply layout) (groupReply layout) layout.scheme.store.representation
      layout.scheme.wordFits (groupsFinished layout).fits))
    ((groupFinish layout).then (SumContext.mergeRight (groupReply layout) (groupReply layout) layout.scheme.store.representation
      layout.scheme.wordFits (groupsFinished layout).fits))
    layout.scheme.wordFits (Handler.Dispatch.groupOutput layout).fits).viewOutput (groupsFinished layout) (groupsFinishValue layout)
      (by intro value; cases value <;> rfl)

def finished : Handler.Dispatch.Output layout → Reply layout × layout.scheme.store.Value
  | .inl value => (.inl (randomFinishValue layout value).1, (randomFinishValue layout value).2)
  | .inr value => (.inr (groupsFinishValue layout value).1, (groupsFinishValue layout value).2)
def finish : Realizer .unit (Handler.Dispatch.output layout) (output layout) (finished layout) :=
  (branchRealizer .unit (by decide) (Handler.Dispatch.randomPacket layout) (Handler.Dispatch.groupOutput layout) (output layout)
    ((randomFinish layout).then (SumContext.mergeLeft (randomReply layout) (groupReplies layout) layout.scheme.store.representation
      layout.scheme.wordFits (output layout).fits))
    ((groupsFinish layout).then (SumContext.mergeRight (randomReply layout) (groupReplies layout) layout.scheme.store.representation
      layout.scheme.wordFits (output layout).fits))
    layout.scheme.wordFits (Handler.Dispatch.output layout).fits).viewOutput (output layout) (finished layout)
      (by intro value; cases value <;> rfl)

variable [DecidableEq M] [DecidableEq G]
def ready (value : Packet layout) : Prop :=
  match value.1 with
  | .inl _ => True
  | .inr (.inl args) => layout.hash.admissible (Handler.hashArgument (args.val, value.2.val))
  | .inr (.inr args) => layout.signing.admissible (Handler.signingArgument (args.val, value.2.val))
instance : DecidablePred (ready layout) := fun value => by
  rcases value with ⟨args | (args | args), saved⟩ <;> dsimp [ready] <;> infer_instance

def serviceRequest (value : Packet layout) (valid : ready layout value) : Handler.Dispatch.Input layout :=
  match value with
  | (.inl args, saved) => .inl ⟨(args.val, saved.val), args.property, saved.property⟩
  | (.inr (.inl args), saved) => .inr (.inl ⟨(args.val, saved.val), ⟨args.property, saved.property⟩, valid⟩)
  | (.inr (.inr args), saved) => .inr (.inr ⟨(args.val, saved.val), ⟨args.property, saved.property⟩, valid⟩)
theorem request_bytes (value : Packet layout) (valid : ready layout value) :
    (Handler.Dispatch.input layout).encoding.encode (serviceRequest layout value valid) =
      (raw layout).encoding.encode (prepared layout value) := by
  rcases value with ⟨args | (args | args), saved⟩ <;> rfl

def admitted : Representation w {value : Packet layout // ready layout value} := (input layout).restrict (ready layout)
def prepareService : Realizer .unit (admitted layout) (Handler.Dispatch.input layout)
    (fun value => serviceRequest layout value.val value.property) :=
  ((prepare layout).viewInput (admitted layout) Subtype.val (fun _ => rfl)).viewOutput (Handler.Dispatch.input layout)
    (fun value => serviceRequest layout value.val value.property) (fun value => request_bytes layout value.val value.property)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerPackets
