import Signatures.Runtime.Caliper.SchnorrAGMFullProgram

/-! Empty-store initialization establishes the caller's capacity reservation.
Only local query legality and continuation invariants remain caller obligations;
the complete reduction's correctness is derived by composition. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (routines : Routines layout) (caller : Caller layout)

structure Caller.Invariant (fuel : Nat) where
  domain : Nat → Nat → Nat → layout.Request × A → Prop
  allowed : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
    CallerHandler.Allowed layout.service hashes signatures q
  advance : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
    ∀ represented original, CallerHandler.replyMatches layout.service q represented original →
      SchnorrAGM.Caller.HeadValid layout.service domain remaining
        (hashes - CallerHandler.hashCharge layout.service q) (signatures - CallerHandler.signCharge layout.service q)
        (caller.advance (c, represented))
  initial : ∀ value, SchnorrAGM.Caller.HeadValid layout.service domain fuel qH qS (caller.initial value)

omit [DecidableEq F] [DecidableEq M] [DecidableEq G] in
theorem start_reserved (value : layout.service.scheme.config.Value) :
    CallerHandler.Reserved layout.service qH qS (start layout routines value).2 :=
  ⟨{}, rfl, layout.service.scheme.initial_reserved⟩
omit [DecidableEq F] [DecidableEq M] [DecidableEq G] in
theorem admitted_reserved (value : layout.service.scheme.config.Value × layout.service.scheme.store.Value)
    (valid : admitted layout routines value) : CallerHandler.Reserved layout.service qH qS value.2 := by
  rw [show value.2 = (start layout routines value.1).2 from valid]
  exact start_reserved layout routines value.1
omit [DecidableEq F] [DecidableEq M] [DecidableEq G] in
theorem start_stored (value : layout.service.scheme.config.Value) :
    CallerHandler.stored layout.service (start layout routines value).2 =
      (value.val, ({} : Signatures.Runtime.SchnorrAGM.State F G M)) := by
  change (value.val, decodeState (encodeState ({} : Signatures.Runtime.SchnorrAGM.State F G M))) = _
  rw [decode_encodeState]

variable [SampleableType F] (sampler : Interactive.Code w)
    (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (sampleCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input w).representation
      layout.service.scheme.scalar.representation (fun _ => sampleSource) sampler)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (fuel : Nat) (invariant : Caller.Invariant layout caller fuel)

include sampleCorrect uniform invariant in
theorem tail_refines : Interactive.RefinesOn (admitted layout routines) layout.service.random.port .unit
    (input layout) layout.service.scheme.scalar.representation (tailSource layout routines caller sampleSource fuel)
    (tail layout routines caller sampler fuel) :=
  CallerExtraction.refines layout routines.handler routines.sub routines.divide routines.subNames.buffers routines.divNames.buffers
    sampleSource uniform invariant.domain invariant.allowed caller.advance invariant.advance caller.initial fuel
    (admitted layout routines) (fun value _ => invariant.initial value.1) (admitted_reserved layout routines)
    sampler sampleCorrect caller.continuation caller.localNameFits layout.service.scheme.config.representation
    caller.initialCode caller.initialNameFits (inputFits layout)

include sampleCorrect uniform invariant in
theorem refines : Interactive.Refines layout.service.random.port .unit layout.service.scheme.config.representation
    layout.service.scheme.scalar.representation (source layout routines caller sampleSource fuel)
    (program layout routines caller sampler fuel) := by
  have composed := ((setup_refines layout routines).on (fun _ => True)).seq
    (tail_refines layout routines caller sampler sampleSource sampleCorrect uniform fuel invariant)
    (by
      intro value _ answer reached
      obtain rfl : answer = start layout routines value := by
        simpa only [support_pure, Set.mem_singleton_iff] using reached
      rfl)
  intro tape value before holds
  simpa only [pure_bind, source, program] using composed tape value trivial before holds

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
