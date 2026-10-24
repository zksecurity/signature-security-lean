import Proofs.Runtime.GeneralWeighted
import Proofs.Runtime.BackendLanguage
import Proofs.Runtime.Arithmetic

/-! Native request and reply adapters for weighted signature callers. Hash and
signing requests have independently selected represented types. Random sampling
uses one runtime-selected implementation, with no table indexed by arities. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM

open BackendProgram

abbrev GeneralIndex (ι M G₁ : Type) (randomBound : Nat) :=
  Σ i : GeneralRequest ι M randomBound, (generalSpec ι M G₁ randomBound).Range i

abbrev BoundedRandomReply (randomBound : Nat) := Σ n : Fin (randomBound + 1), Fin (n.val + 1)

def tagRandom {ι M G₁ : Type} {randomBound : Nat} (r : BoundedRandomReply randomBound) :
    GeneralIndex ι M G₁ randomBound := ⟨.inl (.inl r.1), r.2⟩

def tagHash {ι M G₁ : Type} {randomBound : Nat} (r : ι × G₁) :
    GeneralIndex ι M G₁ randomBound := ⟨.inl (.inr r.1), r.2⟩

def tagSign {ι M G₁ : Type} {randomBound : Nat} (r : M × G₁) :
    GeneralIndex ι M G₁ randomBound := ⟨.inr r.1, r.2⟩

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type} (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (indexTy messageTy : Ty CryptoAtom)

def generalPositions (randomBound : Nat) :
    C.Str (GeneralRequest (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) :=
  StepClass.HasSum.sum (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty indexTy))
    (rep.ty messageTy)

variable {randomBound : Nat} {Input Output : Type}
  (bd : Boundary C (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
    (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input Output)

structure NativePorts where
  randomReply : C.Str (BoundedRandomReply randomBound)
  request : Q.Realizer bd.pos (generalPositions rep indexTy messageTy randomBound) id
  randomTag : Q.Realizer randomReply bd.idx tagRandom
  hashTag : Q.Realizer (StepClass.HasProd.prod (rep.ty indexTy) (rep.ty point₁)) bd.idx tagHash
  signTag : Q.Realizer (StepClass.HasProd.prod (rep.ty messageTy) (rep.ty point₁)) bd.idx tagSign

variable {iface : Interface (C := C) unifSpec} (ports : NativePorts (Q := Q) rep indexTy messageTy bd)

structure BoundedSampler where
  code : Code Q unifSpec iface (rep.ty (boundedNat randomBound)) ports.randomReply
  denote : ∀ n, code.denote n =
    (fun reply => (⟨n, reply⟩ : BoundedRandomReply randomBound)) <$>
      (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1)))

end Signatures.Runtime.WeightedAGM
