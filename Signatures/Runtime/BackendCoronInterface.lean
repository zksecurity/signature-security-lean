import Signatures.Runtime.BackendCoronDescription
import Signatures.Runtime.GeneralCoronCorrectness

/-! Explicit data-code boundaries for general signature callers. The caller's
internal algorithm is unrestricted by the wrapper language. Request decoding
and response tagging carry actual realizers, and the runtime-selected uniform
range uses one implemented sampling primitive, not an enumerated sampler table.
Costs, encoded widths, and descriptions of these individual components are
separate obligations; no complete handler implementation is an input field. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron

open BackendProgram

abbrev GeneralIndex (M G₁ : Type) (randomBound : Nat) := Σ i : GeneralRequest M randomBound, (generalSpec M G₁ randomBound).Range i

abbrev BoundedRandomReply (randomBound : Nat) := Σ n : Fin (randomBound + 1), Fin (n.val + 1)

def tagRandom {M G₁ : Type} {randomBound : Nat} (r : BoundedRandomReply randomBound) :
    GeneralIndex M G₁ randomBound := ⟨.inl (.inl r.1), r.2⟩

def tagGroup {M G₁ : Type} {randomBound : Nat} (signing : Bool) (r : M × G₁) :
    GeneralIndex M G₁ randomBound :=
  if signing then ⟨.inr r.1, r.2⟩ else ⟨.inl (.inr r.1), r.2⟩

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

def generalPositions (randomBound : Nat) : C.Str (GeneralRequest M randomBound) :=
  StepClass.HasSum.sum (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) (rep.ty message)

variable {randomBound : Nat} {Input Output : Type}
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)

structure NativePorts where
  randomReply : C.Str (BoundedRandomReply randomBound)
  request : Q.Realizer bd.pos (generalPositions rep randomBound) id
  randomTag : Q.Realizer randomReply bd.idx tagRandom
  groupTag : (signing : Bool) →
    Q.Realizer (StepClass.HasProd.prod (rep.ty message) (rep.ty point₁)) bd.idx (tagGroup signing)

variable {iface : Interface (C := C) unifSpec} (ports : NativePorts (Q := Q) rep bd)

structure BoundedSampler where
  code : Code Q unifSpec iface (rep.ty (boundedNat randomBound)) ports.randomReply
  denote : ∀ n, code.denote n =
    (fun reply => (⟨n, reply⟩ : BoundedRandomReply randomBound)) <$> (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1)))

end Signatures.Runtime.Coron
