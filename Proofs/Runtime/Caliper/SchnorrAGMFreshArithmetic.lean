import Proofs.Runtime.Caliper.SchnorrAGMFreshZero

/-! Executed fresh-entry arithmetic. Addition is the only supplied field
routine; comparison, Boolean update, retained state and final copies are built
from Caliper instructions. No current challenge or explanation enters the code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} [Zero F] [Add F] [DecidableEq F]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)

def holdZero : Realizer .unit (added layout) (flagged layout)
    (fun value => (decide (value.1.val = 0), value.2)) :=
  (isZero layout zeroValid).retain (by decide) (input layout) layout.wordFits
    (by have := (zero_names layout zeroValid).buffers; have := layout.wordFits
        change max 2 (isZero layout zeroValid).code.memBound < _; omega)
    (added layout).fits (flagged layout).fits

def holdMerge : Realizer .unit (merging layout) (flagged layout)
    (fun value => (value.1.1 || value.1.2, value.2)) :=
  (Boolean.or layout.wordFits).retain (by decide) (input layout) layout.wordFits
    (by change 2 < 2 ^ w; have := layout.wordFits; omega)
    (merging layout).fits (flagged layout).fits

variable (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)

def holdAdd : Realizer .unit (adding layout) (added layout)
    (fun value => (⟨value.1.val.1 + value.1.val.2, add.preserves value.1.val value.1.property⟩, value.2)) :=
  add.program.retain (by decide) (input layout) layout.wordFits
    (by have := layout.wordFits; change max 2 add.program.code.memBound < _; omega)
    (adding layout).fits (added layout).fits

def arithmetic : Realizer .unit (input layout) (Cache.model layout).freshOutput
    (fun value => Cache.freshValue layout value.1 value.2) :=
  ((((((prepareAdd layout).then (holdAdd layout add addBuffers slotsFit)).then
    (holdZero layout zeroValid)).then (prepareMerge layout)).then (holdMerge layout)).then
      (finish layout)).viewOutput _ (fun value => Cache.freshValue layout value.1 value.2) (fun _ => rfl)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
