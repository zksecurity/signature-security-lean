import Signatures.Runtime.Caliper.SchnorrROMTapeCallerMemory
import Signatures.Runtime.Caliper.SchnorrROMTapeCallerSource
import Signatures.Runtime.SchnorrPrivateReplay

/-! Fully constructed private replay. Private requests cannot enter the scalar
draw branch, so a charged constant suffices there. Neither correctness nor the
resource account assumes an external sampler or a completed replay routine. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateQuery
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

def unusedScalar : Constructed layout.unit layout.scalar (fun _ => 0) :=
  Constructed.constant layout.unit layout.scalar ⟨0, zeroValid⟩ layout.wordFits
def unusedCode : Interactive.Code w := .compute (unusedScalar layout zeroValid).implementation.program.code
def unusedWords : Nat := (unusedScalar layout zeroValid).budget.words + 1

theorem unused_refines : Interactive.Refines (Fresh.port layout) .unit layout.unit.representation
    layout.scalar.representation (fun _ => pure ⟨0, zeroValid⟩) (unusedCode layout zeroValid) :=
  Interactive.Refines.compute (Fresh.port layout) .unit (unusedScalar layout zeroValid).implementation.program

theorem unused_time : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation
    (unusedCode layout zeroValid) (unusedScalar layout zeroValid).budget.time :=
  Interactive.TimeBound.compute (port := Fresh.port layout) (cost := .unit)
    (unusedScalar layout zeroValid).implementation.program _
    (unusedScalar layout zeroValid).bounded.time_le

theorem unused_words : ((unusedCode layout zeroValid).lower (Fresh.port layout)).descriptionWords ≤ unusedWords layout zeroValid := by
  have bound := (unusedScalar layout zeroValid).bounded.code_le
  simp only [unusedCode, Interactive.Code.lower, WordIO.Code.descriptionWords_compute, unusedWords]
  omega

theorem unused_names : WordIO.NamesBound ((unusedCode layout zeroValid).lower (Fresh.port layout)) (unusedWords layout zeroValid) := by
  have named : WordIO.NamesAccounted ((unusedCode layout zeroValid).lower (Fresh.port layout)) 0 :=
    WordIO.NamesAccounted.compute ((unusedScalar layout zeroValid).names 0)
  have stored := unused_words layout zeroValid
  exact ⟨by have := named.registers; change _ ≤ 0 + _ at this; omega,
    by have := named.buffers; change _ ≤ 0 + _ at this; omega⟩

def code := Caller.privateCode layout zeroValid (unusedCode layout zeroValid)
def source := Caller.privateDenote layout zeroValid (pure ⟨0, zeroValid⟩)
def timeBudget := Caller.privateTime layout zeroValid (unusedScalar layout zeroValid).budget.time
def codeBudget := Caller.privateWords layout zeroValid (unusedWords layout zeroValid)
def nameBudget := Caller.nameSlots layout zeroValid (unusedWords layout zeroValid) (unusedWords layout zeroValid)

theorem refines : Interactive.Refines (Fresh.port layout) .unit (Caller.privateInput layout).representation
    (Reply.privateOutput layout).representation (source layout zeroValid) (code layout zeroValid) :=
  Caller.private_refines layout zeroValid (unused_refines layout zeroValid)

theorem time_bound : Interactive.TimeBound (Fresh.port layout) .unit (Caller.privateInput layout).representation
    (code layout zeroValid) (timeBudget layout zeroValid) :=
  Caller.private_time layout zeroValid (unused_refines layout zeroValid) (unused_time layout zeroValid)

theorem code_bound : ((code layout zeroValid).lower (Fresh.port layout)).descriptionWords ≤ codeBudget layout zeroValid :=
  Caller.private_words layout zeroValid _ (unused_words layout zeroValid)

theorem names : WordIO.NamesAccounted ((code layout zeroValid).lower (Fresh.port layout)) (nameBudget layout zeroValid) :=
  Caller.private_names layout zeroValid _ (unused_words layout zeroValid) (unused_names layout zeroValid)

theorem buffers : ((code layout zeroValid).lower (Fresh.port layout)).memBound ≤ 8 := by
  have bound := Caller.private_buffers layout zeroValid (unusedCode layout zeroValid)
  change ((code layout zeroValid).lower (Fresh.port layout)).memBound ≤ _ at bound
  have constant := (unusedScalar layout zeroValid).buffers_le
  change _ ≤ 2 at constant
  change _ ≤ max 8 ((unusedScalar layout zeroValid).implementation.program.code.memBound + 2) at bound
  omega

theorem descriptionFits : ((code layout zeroValid).lower (Fresh.port layout)).DescriptionFits := by
  apply Caller.private_descriptionFits layout zeroValid
    (unusedCode layout zeroValid) (.compute (unusedScalar layout zeroValid).implementation.program.description_fits)
  have bound := (unusedScalar layout zeroValid).buffers_le
  change _ ≤ 2 at bound
  change (unusedScalar layout zeroValid).implementation.program.code.memBound + 1 < 2 ^ w
  have := layout.wordFits
  omega

/-- The constructed query equals the original private oracle on every admitted
tape, including cells whose stored natural payload exceeds the query range. -/
theorem source_eq (n : Nat) (state : Schnorr.RawTape.State F)
    (valid : (Caller.privateInput layout).valid (Caller.rawPrivate n state)) :
    Subtype.val <$> source layout zeroValid ⟨Caller.rawPrivate n state, valid⟩ =
      Caller.privateResult n <$> (Schnorr.RawTape.Private.oracle n).run state := by
  rw [Schnorr.RawTape.Private.oracle_eq (Fresh.sample layout (pure ⟨0, zeroValid⟩)) (fun _ => rfl)]
  exact Caller.private_source layout zeroValid _ n state valid

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateQuery
