import Signatures.Runtime.BackendSchnorrROMHandlerComponents
import Signatures.Runtime.GeneralCaller

/-! Actual request/reply ports for arbitrary ordinary-ROM callers. Random
arities are runtime naturals, and hash/signing replies retain their distinct
types. Every conversion is supplied as backend code, never as a free cast. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeInterface

open BackendProgram NativeComponents

abbrev sourceSpec (F G M : Type) := FiatShamir.cmaOracleSpec M G F F
abbrev Request (G M : Type) := (Nat ⊕ (M × G)) ⊕ M
abbrev Response (F G M : Type) := (sourceSpec F G M).toPFunctor.Idx

def randomTag {F G M : Type} (p : Nat × Nat) : Response F G M :=
  ⟨.inl (.inl p.1), RawTape.NativeUniform.decodeNat p.1 p.2⟩

def hashTag {F G M : Type} (p : (M × G) × F) : Response F G M :=
  ⟨.inl (.inr p.1), p.2⟩

def signingTag {F G M : Type} (p : M × G × F) : Response F G M :=
  ⟨.inr p.1, p.2⟩

def defaultReply {F G M : Type} [Zero F] [Zero G] (q : Request G M) : (sourceSpec F G M).Range q :=
  match q with
  | .inl (.inl n) => (0 : Fin (n + 1))
  | .inl (.inr _) => 0
  | .inr _ => (0, 0)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def positions : C.Str (Request G₁ M) :=
  StepClass.HasSum.sum (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey)) (rep.ty message)

variable (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)

structure Ports where
  request : Q.Realizer bd.pos (positions rep) id
  randomTag : Q.Realizer (rep.ty (.pair .nat .nat)) bd.idx randomTag
  hashTag : Q.Realizer (rep.ty (.pair hashKey scalar)) bd.idx hashTag
  signingTag : Q.Realizer (rep.ty (.pair message signatureTy)) bd.idx signingTag

end Signatures.Runtime.Schnorr.ListROM.NativeInterface
