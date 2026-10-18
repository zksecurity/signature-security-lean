import Signatures.Runtime.Caliper.BLSDispatchSchemes
import Signatures.Runtime.Caliper.UniformQuery

/-! The complete random/hash/sign service for BLS AGM, with a common uniform
port. Requests and replies have stored tags. The private store is returned on
every branch; random forwarding copies it without changing the cache or logs.
This service is the handler to be linked to the caller, not a whole reduction. -/

namespace Signatures.Runtime.CaliperBackend.BLSOracle
open Caliper BoundedSource OracleComp OracleSpec

section Layouts

variable {w : Nat} {M R C G : Type} [DecidableEq M]
    (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)

def width : Nat := layout.width + 3

omit [DecidableEq M] in
theorem store_le : layout.store.representation.encoding.words ≤ layout.width := by
  rw [BLSReply.Layouts.store_words]
  dsimp only [BLSReply.Layouts.width]
  rw [BLSReply.Layouts.lookup_width]
  omega

omit [DecidableEq M] in
theorem storageFits : 2 + layout.store.representation.encoding.words < 2 ^ w := by
  have room := layout.storageFits
  have store := store_le layout
  have words := layout.cache.wordFits
  change 16 * layout.width < 2 ^ w at room
  omega

def randomInput : Representation w (Fin (randomBound + 1) × layout.store.Value) :=
  UniformQuery.input randomBound layout.cache.wordFits randomFits layout.store.representation (storageFits layout)

def randomOutput : Representation w (UniformQuery.Reply randomBound × layout.store.Value) :=
  UniformQuery.output randomBound layout.cache.wordFits randomFits layout.store.representation (storageFits layout)

omit [DecidableEq M] in
theorem group_output_le : layout.output.representation.encoding.words ≤ layout.width := by
  change layout.point.representation.encoding.words + layout.store.representation.encoding.words ≤ _
  rw [BLSReply.Layouts.store_words]
  dsimp only [BLSReply.Layouts.width]
  rw [BLSReply.Layouts.lookup_width]
  omega

theorem inputFits : 1 + max (randomInput layout randomBound randomFits).encoding.words
    (BLSDispatch.input layout default).representation.encoding.words < 2 ^ w := by
  have store := store_le layout
  have left := layout.input_le default.val false
  have right := layout.input_le default.val true
  have room := layout.storageFits
  have words := layout.cache.wordFits
  change 1 + max (1 + layout.store.representation.encoding.words)
    (1 + max (layout.input default.val false).representation.encoding.words (layout.input default.val true).representation.encoding.words) < 2 ^ w
  change 16 * layout.width < 2 ^ w at room
  omega

omit [DecidableEq M] in
theorem outputFits : 1 + max (randomOutput layout randomBound randomFits).encoding.words
    layout.output.representation.encoding.words < 2 ^ w := by
  have store := store_le layout
  have group := group_output_le layout
  have room := layout.storageFits
  have words := layout.cache.wordFits
  change 1 + max (2 + layout.store.representation.encoding.words) layout.output.representation.encoding.words < 2 ^ w
  change 16 * layout.width < 2 ^ w at room
  omega

def input := (randomInput layout randomBound randomFits).sum (BLSDispatch.input layout default).representation
  (width_pos layout.cache.wordFits) (inputFits layout default randomBound randomFits)

def output := (randomOutput layout randomBound randomFits).sum layout.output.representation
  (width_pos layout.cache.wordFits) (outputFits layout randomBound randomFits)

def randomTag : Realizer .unit (randomOutput layout randomBound randomFits) (output layout randomBound randomFits) Sum.inl :=
  inlRealizer .unit (by decide) _ _ layout.cache.wordFits (outputFits layout randomBound randomFits)

def groupTag : Realizer .unit layout.output.representation (output layout randomBound randomFits) Sum.inr :=
  inrRealizer .unit (by decide) _ _ layout.cache.wordFits (outputFits layout randomBound randomFits)

end Layouts

variable {w : Nat} {C G : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)

def randomCode : Interactive.Code w :=
  .seq (UniformQuery.forward randomBound layout.cache.wordFits randomFits layout.store.representation)
    (.compute (randomTag layout randomBound randomFits).code)

def groupCode : Interactive.Code w :=
  .seq (BLSDispatch.code layout default P comparison correct (UniformQuery.port randomBound layout.cache.wordFits randomFits) draw response responseBuffers reserve)
    (.compute (groupTag layout randomBound randomFits).code)

def code : Interactive.Code w := Interactive.dispatch
  (randomCode layout randomBound randomFits)
  (groupCode layout default randomBound randomFits P comparison correct response responseBuffers reserve draw)
  (randomInput layout randomBound randomFits).encoding.words (BLSDispatch.input layout default).representation.encoding.words

def denote (drawSource : ProbComp layout.cache.value.Value) :
    (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value →
      ProbComp ((UniformQuery.Reply randomBound × layout.store.Value) ⊕ layout.output.Value) :=
  Sum.elim (fun value => Sum.inl <$> UniformQuery.forwardSource randomBound value)
    (fun value => Sum.inr <$> BLSDispatch.denote layout default P comparison correct response responseBuffers reserve drawSource value)

omit [DecidableEq (key.Value base)] in
theorem random_refines : Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
    (randomInput layout randomBound randomFits) (output layout randomBound randomFits)
    (fun value => Sum.inl <$> UniformQuery.forwardSource randomBound value) (randomCode layout randomBound randomFits) := by
  simpa only [randomCode, randomInput, bind_pure_comp] using
    (UniformQuery.forward_refines randomBound layout.cache.wordFits randomFits layout.store.representation (storageFits layout)).seq
      (Interactive.Refines.compute _ .unit (randomTag layout randomBound randomFits))

theorem group_refines (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw) :
    Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      (BLSDispatch.input layout default).representation (output layout randomBound randomFits)
      (fun value => Sum.inr <$> BLSDispatch.denote layout default P comparison correct response responseBuffers reserve drawSource value)
      (groupCode layout default randomBound randomFits P comparison correct response responseBuffers reserve draw) := by
  simpa only [groupCode, bind_pure_comp] using
    (BLSDispatch.refines layout default P comparison correct _ draw response responseBuffers reserve drawSource drawCorrect).seq
      (Interactive.Refines.compute _ .unit (groupTag layout randomBound randomFits))

theorem refines (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw) :
    Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      (input layout default randomBound randomFits) (output layout randomBound randomFits)
      (denote layout default randomBound P comparison correct response responseBuffers reserve drawSource)
      (code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw) :=
  Interactive.Refines.dispatch _ _ _ (random_refines layout randomBound randomFits)
    (group_refines layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawSource drawCorrect)
    (width_pos layout.cache.wordFits) (inputFits layout default randomBound randomFits)

end Signatures.Runtime.CaliperBackend.BLSOracle
