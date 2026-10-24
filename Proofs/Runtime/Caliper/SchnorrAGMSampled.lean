import Proofs.Runtime.Caliper.SchnorrAGMSigningArithmeticBounds
import Proofs.Runtime.Caliper.SchnorrAGMHistoriesBounds
import Proofs.Runtime.Caliper.SchnorrAGMProgrammingBounds

/-! The complete deterministic signing program after the two scalar draws.
Arithmetic, chronological histories and cache programming are executed in
sequence. Domain guards carry the available slots through those stages without
adding runtime instructions or changing stored bytes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampled
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    [DecidableEq M] [DecidableEq G] (layout : Histories.Layouts w M F G qH qS)

def cacheRoom (args : Work M F G) : Prop := layout.scheme.cache.admissible args.1
instance cacheRoomDecidable : DecidablePred (cacheRoom layout) := by intro args; unfold cacheRoom; infer_instance
def admissible (args : Input M F G) : Prop := layout.room (Arithmetic.value args) ∧ cacheRoom layout (Arithmetic.value args)
instance admissibleDecidable : DecidablePred (admissible layout) := by intro args; unfold admissible; infer_instance
def input : Layout w (Input M F G) := layout.signing.input.restrict (admissible layout)
def work : Layout w (Work M F G) := layout.input.restrict (cacheRoom layout)
def value (args : Input M F G) := Programming.value (Signatures.Runtime.SchnorrAGM.Native.Signing.historiesValue (Arithmetic.value args))

def histories : Implementation .unit (work layout) (Programming.input layout)
    Signatures.Runtime.SchnorrAGM.Native.Signing.historiesValue :=
  ((Histories.implementation layout).restrictInput (cacheRoom layout)).restrictOutput
    (fun args => layout.scheme.cache.admissible args.1) (fun _ valid => valid.2)

variable (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def arithmetic : Implementation .unit (input layout) (work layout) Arithmetic.value :=
  (((Arithmetic.implementation layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).restrictInput
    (admissible layout)).restrictOutput layout.room (fun _ valid => valid.2.1)).restrictOutput
      (cacheRoom layout) (fun _ valid => valid.2.2)

def implementation : Implementation .unit (input layout) (Programming.output layout) value :=
  (((arithmetic layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).then (histories layout)).then
    (Programming.implementation layout)).castFunction rfl

theorem buffers : (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound ≤
    max 9 (max 3 slots + 3) := by
  have arithmeticBound := Arithmetic.buffers layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
  have historyBound := Histories.buffers layout
  have cacheBound := Programming.buffers layout
  change max (max (Arithmetic.implementation layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound
    (Histories.implementation layout).program.code.memBound) (Programming.implementation layout).program.code.memBound ≤ _
  omega

theorem names {named : Nat} (scaleNames : NamesAccounted scale.program.code named)
    (subNames : NamesAccounted sub.program.code named) (negateNames : NamesAccounted negate.program.code named) :
    NamesAccounted (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code (max 5 named) := by
  have arithmeticNames : NamesAccounted (arithmetic layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code (max 5 named) :=
    (Arithmetic.names layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve named
      scaleNames subNames negateNames).mono (Nat.le_max_right _ _)
  have historyNames : NamesAccounted (histories layout).program.code (max 5 named) := Histories.names layout _
  exact (arithmeticNames.seq historyNames).seq ((Programming.names layout).mono (Nat.le_max_left _ _))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampled

namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampled
variable {w qH qS : Nat} {M F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] (layout : Histories.Layouts w M F G qH qS)

theorem source (args : Input M F G) : value args = Signatures.Runtime.SchnorrAGM.Native.Signing.signedValue args := rfl

theorem signedState (state : Signatures.Runtime.SchnorrAGM.State F G M) (generator publicKey : G) (message : M) (challenge response : F) :
    value ((challenge, response), generator, publicKey, message, Signatures.Runtime.SchnorrAGM.Native.encodeState state) =
      ((response • generator - challenge • publicKey, response),
        Signatures.Runtime.SchnorrAGM.Native.encodeState
          (Signatures.Runtime.SchnorrAGM.signedState state generator publicKey message challenge response)) :=
  Signatures.Runtime.SchnorrAGM.Native.Signing.signedValue_source state generator publicKey message challenge response

theorem reserved_admissible {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes (signatures + 1) state)
    (challenge response : F) (generator publicKey : G) (message : M) :
    admissible layout ((challenge, response), generator, publicKey, message, Signatures.Runtime.SchnorrAGM.Native.encodeState state) :=
  ⟨Histories.reserved_room layout room challenge response generator publicKey message,
    Programming.reserved_admissible layout room challenge response generator publicKey message⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampled
