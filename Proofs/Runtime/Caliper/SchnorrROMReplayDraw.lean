import Proofs.Runtime.Caliper.SchnorrROMEnumeratedReplay
import Proofs.Runtime.Caliper.InteractiveInvariantViews

/-! A public replay draw as a stateful cache routine. Its ordinary state admits
full tapes, while its input invariant reserves one saved cell. Output state
therefore does not incorrectly promise that this spent reservation survives. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.EnumeratedReplay
open Caliper BoundedSource OracleComp OracleSpec PrivateSampler.Enumerated
variable {w : Nat} {F : Type} [Zero F] (params : Parameters w F)

def ready (value : (Read.tapes (tape params)).Value) : Prop := value.val.1.length < params.capacity
instance (value : (Read.tapes (tape params)).Value) : Decidable (ready params value) :=
  inferInstanceAs (Decidable (_ < _))

def admitted (value : (Read.tapes (tape params)).Value) (valid : ready params value) : (Read.store (tape params)).Value :=
  ⟨value.val, ⟨value.property.1, valid⟩, value.property.2⟩

def drawOutput : Representation w ((tape params).scalar.Value × (Read.tapes (tape params)).Value) :=
  (tape params).scalar.representation.prod (Read.tapes (tape params)).representation (Reply.scalarOutput (tape params)).representation.fits

def drawSource (value : (Read.tapes (tape params)).Value) :
    ProbComp ((tape params).scalar.Value × (Read.tapes (tape params)).Value) :=
  if valid : ready params value then
    productView (tape params).scalar (Read.tapes (tape params)) <$>
      Caller.scalarDenote (tape params) trivial (Direct.source params) (admitted params value valid)
  else pure (⟨0, trivial⟩, value)

theorem draw_refines : Interactive.RefinesOn (ready params) (Fresh.port (tape params)) .unit
    (Read.tapes (tape params)).representation (drawOutput params) (drawSource params) (scalarCode params) := by
  have refined := (Caller.scalar_refines (tape params) trivial (Direct.refines params)).viewOutput
    (drawOutput params) (productView (tape params).scalar (Read.tapes (tape params))) (fun _ => rfl)
  intro random value valid before holds
  rw [drawSource, dite_eq_left valid]
  exact refined random (admitted params value valid) before holds

theorem draw_time : Interactive.TimeBoundOn (ready params) (Fresh.port (tape params)) .unit
    (Read.tapes (tape params)).representation (scalarCode params) (Caller.scalarTime (tape params) trivial 26) := by
  intro random value valid before holds
  exact Caller.scalar_time (tape params) trivial (Direct.refines params) (Direct.time_bound params)
    random (admitted params value valid) before holds

theorem draw_source (value : (Read.tapes (tape params)).Value) (valid : ready params value) :
    letI := sampleable params
    (fun answer => (answer.1.val, answer.2.val)) <$> drawSource params value =
      Caller.scalarResult <$> simulateQ _root_.Schnorr.LazyROM.sample
        ((Schnorr.RawTape.oracle (.inr ())).run ⟨value.val.1, value.val.2⟩) := by
  rw [drawSource, dite_eq_left valid]
  exact (PFunctor.FreeM.comp_map (fun answer : (tape params).scalar.Value × (Read.tapes (tape params)).Value =>
    (answer.1.val, answer.2.val)) (productView (tape params).scalar (Read.tapes (tape params)))
    (Caller.scalarDenote (tape params) trivial (Direct.source params) (admitted params value valid))).symm.trans
      (scalar_source params ⟨value.val.1, value.val.2⟩ (admitted params value valid).property)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.EnumeratedReplay
