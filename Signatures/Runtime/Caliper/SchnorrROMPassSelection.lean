import Signatures.Runtime.Caliper.SchnorrROMSelectionMemory

/-! Select directly from the complete pass output. Cutoff writes a rejection;
a returned forgery runs the verified LIVE selector. Moving union padding across
the saved store and dispatching the selected branch are charged instructions. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.PassSelection
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem inputFits : 1 + max (Pairing.unitRepresentation w).encoding.words (ForgeryHash.result config).encoding.words +
    config.handler.store.representation.encoding.words < 2 ^ w := by
  apply config.handler.fits_of_le
  have size := (Selection.sizes config).1
  have positive := Random.positive config
  change (ForgeryHash.result config).encoding.words + config.handler.store.representation.encoding.words ≤ _ at size
  change 1 + max 0 _ + _ ≤ _
  omega
def input : Representation w (Terminal.Output config) :=
  SumContext.input (Pairing.unitRepresentation w) (ForgeryHash.result config)
    config.handler.store.representation config.sampler.wordFits (inputFits config)
def cutoffInput := (Pairing.unitRepresentation w).prod config.handler.store.representation
  (by have := inputFits config; change 0 + _ < _; change 1 + max 0 _ + _ < _ at this; omega)
def distribute := SumContext.distribute (Pairing.unitRepresentation w) (ForgeryHash.result config)
  config.handler.store.representation config.sampler.wordFits (inputFits config)
def rejected : (Selection.result config).Value := ⟨(false, 0), trivial, Nat.zero_lt_succ _⟩
def cutoff : Realizer .unit (cutoffInput config) (Selection.result config).representation (fun _ => rejected config) :=
  ByteRoute.realizer _ _ _ [.literal [0, 0]] config.sampler.wordFits trivial rfl (fun _ => rfl)
theorem widths : (cutoffInput config).encoding.words ≤ (input config).encoding.words ∧
    (ForgeryHash.output config).encoding.words ≤ (input config).encoding.words := by
  change 0 + _ ≤ 1 + max 0 _ + _ ∧ _ + _ ≤ 1 + max 0 _ + _
  omega
theorem pass_bytes {P : Type} (pending : Representation w P) (room : 8 * Terminal.width config pending < 2 ^ w)
    (value : Terminal.Output config) :
    (input config).encoding.encode value = (Terminal.output config pending room).encoding.encode value := rfl

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations config) (qH : Nat) (fits : qH + 1 < 2 ^ w)

def source (qH : Nat) (value : Terminal.Output config) : Bool × Nat :=
  match value.1 with
  | .inl _ => (false, 0)
  | .inr returned => Selection.source qH (Selection.represented config (returned, value.2)).val
include ops fits in
theorem valid (value : Terminal.Output config) : (Selection.result config).valid (source config qH value) := by
  rcases value with ⟨cutoff | returned, saved⟩
  · exact (rejected config).property
  · exact (Selection.implementation config ops qH fits).preserves _ (Selection.represented config (returned, saved)).property
def dispatched := branchRealizer .unit (by decide) (cutoffInput config) (ForgeryHash.output config)
  (Selection.result config).representation (cutoff config) (Selection.realizer config ops qH fits)
    config.sampler.wordFits
    (SumContext.output (Pairing.unitRepresentation w) (ForgeryHash.result config) config.handler.store.representation
      config.sampler.wordFits (inputFits config)).fits
def realizer : Realizer .unit (input config) (Selection.result config).representation
    (fun value => ⟨source config qH value, valid config ops qH fits value⟩) :=
  ((distribute config).then (dispatched config ops qH fits)).viewOutput (Selection.result config).representation
    (fun value => ⟨source config qH value, valid config ops qH fits value⟩)
    (by rintro ⟨cutoff | returned, saved⟩ <;> rfl)
def implementation : Implementation .unit (Layout.all (input config)) (Selection.result config) (source config qH) where
  preserves value _ := valid config ops qH fits value
  program := (realizer config ops qH fits).viewInput (Layout.all (input config)).representation Subtype.val (fun _ => rfl)

theorem buffers : (realizer config ops qH fits).code.memBound ≤ max 8 (ops.slots + 3) := by
  have moved := SumContext.buffers (Pairing.unitRepresentation w) (ForgeryHash.result config)
    config.handler.store.representation config.sampler.wordFits (inputFits config)
  have stopped : (cutoff config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have selected := Selection.buffers config ops qH fits
  have branches := Dispatch.buffers (cutoff config).code (Selection.realizer config ops qH fits).code
    (cutoffInput config).encoding.words (ForgeryHash.output config).encoding.words
  change max (distribute config).code.memBound _ ≤ _
  change (distribute config).code.memBound ≤ 3 at moved
  change (Selection.realizer config ops qH fits).code.memBound ≤ _ at selected
  change (dispatched config ops qH fits).code.memBound ≤
    max 2 (max (cutoff config).code.memBound (Selection.realizer config ops qH fits).code.memBound) at branches
  omega
theorem names : NamesAccounted (realizer config ops qH fits).code (max 3 ops.slots) :=
  ((SumContext.names (Pairing.unitRepresentation w) (ForgeryHash.result config)
    config.handler.store.representation config.sampler.wordFits (inputFits config)).mono (Nat.le_max_left _ _)).seq
    (Dispatch.names (ByteRoute.names _ _ _ _ _ _ _ _ _)
      ((Selection.names config ops qH fits).mono (Nat.le_max_right _ _)) _ _)

end Signatures.Runtime.CaliperBackend.SchnorrROM.PassSelection
