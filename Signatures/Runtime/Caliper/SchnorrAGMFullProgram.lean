import Signatures.Runtime.Caliper.SchnorrAGMCallerExtractionBounds
import Signatures.Runtime.Caliper.SchnorrAGMSetup

/-! The complete single-pass Schnorr AGM program. Initialization, private query
handling, caller control and final extraction are constructed Caliper code.
Only named arithmetic routines and local caller steps are supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)

structure Caller where
  advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A)
  continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance
  localNameFits : continuation.savedBuffer < 2 ^ w
  initial : layout.service.scheme.config.Value → layout.forgery.Value ⊕ (layout.Request × A)
  initialCode : Realizer .unit layout.service.scheme.config.representation (CallerStep.next layout.control) initial
  initialNameFits : initialCode.savedBuffer < 2 ^ w

theorem inputFits : layout.service.scheme.config.representation.encoding.words +
    layout.service.scheme.store.representation.encoding.words < 2 ^ w :=
  layout.service.scheme.initialized.representation.fits
def input : Representation w (layout.service.scheme.config.Value × layout.service.scheme.store.Value) :=
  layout.service.scheme.config.representation.prod layout.service.scheme.store.representation (inputFits layout)
def setupView (value : layout.service.scheme.initialized.Value) :
    layout.service.scheme.config.Value × layout.service.scheme.store.Value :=
  (⟨value.val.1, value.property.1⟩, ⟨value.val.2, value.property.2⟩)
theorem setup_bytes (value : layout.service.scheme.initialized.Value) :
    (input layout).encoding.encode (setupView layout value) =
      layout.service.scheme.initialized.representation.encoding.encode value := rfl

variable [Zero F] [One F] [Mul F] [Add F] [Sub F] [Div F] [Neg F] [SMul F G] [Sub G]
    [DecidableEq F] [DecidableEq M] [DecidableEq G]
structure Routines where
  handler : Handler.Operations layout.service
  oneValid : layout.service.scheme.scalar.valid 1
  sub : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 - value.2)
  divide : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 / value.2)
  subNames : NamesBound sub.program.code handler.slots
  divNames : NamesBound divide.program.code handler.slots

variable (routines : Routines layout) (caller : Caller layout)
def start (value : layout.service.scheme.config.Value) :=
  setupView layout (Setup.initialized layout.service.scheme routines.handler.zeroValid routines.oneValid value)
def tail (sampler : Interactive.Code w) (fuel : Nat) : Interactive.Code w :=
  CallerExtraction.program layout routines.handler routines.sub routines.divide
    routines.subNames.buffers routines.divNames.buffers sampler caller.advance caller.continuation caller.localNameFits
    layout.service.scheme.config.representation caller.initial caller.initialCode caller.initialNameFits (inputFits layout) fuel
def program (sampler : Interactive.Code w) (fuel : Nat) : Interactive.Code w :=
  .seq (.compute (Setup.code layout.service.scheme routines.handler.zeroValid routines.oneValid).code)
    (tail layout routines caller sampler fuel)
def tailSource (sampler : ProbComp layout.service.scheme.scalar.Value) (fuel : Nat) :=
  CallerExtraction.denote layout routines.handler routines.sub routines.divide routines.subNames.buffers
    caller.advance caller.initial fuel sampler
def source (sampler : ProbComp layout.service.scheme.scalar.Value) (fuel : Nat)
    (value : layout.service.scheme.config.Value) : ProbComp layout.service.scheme.scalar.Value :=
  tailSource layout routines caller sampler fuel (start layout routines value)
def admitted (value : layout.service.scheme.config.Value × layout.service.scheme.store.Value) : Prop :=
  value.2 = (start layout routines value.1).2

omit [DecidableEq F] [DecidableEq M] [DecidableEq G] in
theorem setup_refines :
    Interactive.Refines layout.service.random.port .unit layout.service.scheme.config.representation (input layout)
      (fun value => pure (start layout routines value))
      (.compute (Setup.code layout.service.scheme routines.handler.zeroValid routines.oneValid).code) :=
  (Interactive.Refines.compute layout.service.random.port .unit
    (Setup.code layout.service.scheme routines.handler.zeroValid routines.oneValid)).viewOutput
      (input layout) (setupView layout) (setup_bytes layout)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
