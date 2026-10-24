import Proofs.Runtime.BackendSchnorrPrivateSampling
import Proofs.Runtime.BackendStateSimulationDescription
import Proofs.Runtime.BackendLanguageSize

/-! Static bounds count the original sampler, each installed tape handler and
the implemented dynamic request/reply conversions. No arity is enumerated. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativePrivate

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : Ports (Q := Q) rep (iface := iface))
  (sizes : DescriptionSize Q) (allowance : Nat)

def handlerDescription : Nat :=
  NativeUniform.descriptionBound rep cost primitive uniform sizes allowance +
    sizes.localSize ports.arity + sizes.localSize ports.reply + 14 * allowance + 11

omit QD in
theorem handler_description (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (handler rep data cost primitive uniform ports).descriptionSize sizes ≤
      handlerDescription rep cost primitive uniform ports sizes allowance := by
  have hctx := Language.withContext_descriptionSize sizes allowance laws
    (rep.ty NativeUniform.stateTy) (Q.identity rep.data.nat)
    (NativeUniform.code rep data cost primitive uniform)
  have hu := NativeUniform.description rep data cost primitive uniform sizes allowance laws dataLaws
  have hi := laws.identity rep.data.nat
  dsimp only [handler, Code.descriptionSize, handlerDescription]
  omega

theorem description (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (distribute : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T),
      sizes.localSize (QD.distribute a b t) ≤ allowance)
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q unifSpec iface a b) :
    (code rep data cost primitive uniform ports program).descriptionSize sizes ≤
      (handlerDescription rep cost primitive uniform ports sizes allowance + 18 * allowance + 6) *
        program.descriptionSize sizes := by
  exact (StateSimulation.compile_description sizes allowance laws (rep.ty NativeUniform.stateTy)
    (handler rep data cost primitive uniform ports) distribute program).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.add_le_add_right
        (handler_description rep data cost primitive uniform ports sizes allowance laws dataLaws) _) _))

end Signatures.Runtime.Schnorr.RawTape.NativePrivate
