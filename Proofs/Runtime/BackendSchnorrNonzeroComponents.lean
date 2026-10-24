import Proofs.Runtime.BackendSchnorrNonzeroPrivatePolynomial
import Proofs.Runtime.BackendSchnorrROMHandlerComponents
import Proofs.Runtime.SchnorrNonzeroListPass

/-! Install the nonzero signer in the common configuration/cache/tape store.
The executed adapters retain the public configuration and untouched live cache.
Both original samplers share the same private tape with attacker randomness. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeComponents

open BackendProgram RawTape ListROM.NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def signing : Code Q unifSpec iface (rep.ty (withStore message)) (rep.ty (withStore signatureTy)) :=
  wrap rep data cost primitive keepCacheTy signingInput signingOutput
    (NativeSigning.code rep data cost primitive uniform ports fieldSampler nonzeroSampler)

theorem signing_denote (msg : M) (saved : ListROM.Shared.Store F G₁ M) :
    (signing rep data cost primitive uniform ports fieldSampler nonzeroSampler).denote (msg, saved) =
      (fun p => (p.1.1, (saved.1.1, p.1.2, saved.1.2.2), p.2)) <$>
        (NativeSigning.code rep data cost primitive uniform ports fieldSampler nonzeroSampler).denote
          ((msg, saved.1.1.1, saved.1.1.2, saved.1.2.1, ()), saved.2) := by
  simp only [signing, wrap, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

/-- All replies, both caches, configuration and the full tape have the exact
finite-pass source semantics for nonzero signing, including cache collisions. -/
theorem signing_source [SampleableType F] [SampleableType Fˣ]
    (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
    (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
    (msg : M) (saved : ListROM.Shared.Store F G₁ M) :
    (signing rep data cost primitive uniform ports fieldSampler nonzeroSampler).denote (msg, saved) =
      (ListROM.Shared.interpret (handler (G₂ := G₂) (K := K) (.inr msg))).run saved := by
  rw [signing_denote, NativeSigning.code_source rep data cost primitive uniform ports
    fieldSampler nonzeroSampler fieldLaw nonzeroLaw]
  change _ = (fun p => (p.1.1, p.1.2, p.2)) <$>
    ListROM.Shared.tapeRun
      ((fun p => (p.1, (saved.1.1, p.2, saved.1.2.2))) <$>
        liftRandom (NonzeroSigning.source saved.1.1.1 saved.1.1.2 msg saved.1.2.1)) saved.2
  rw [ListROM.Shared.tapeRun_map, Functor.map_map]

theorem signing_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T),
      sizes.localSize (QD.distribute a b t) ≤ allowance) :
    (signing rep data cost primitive uniform ports fieldSampler nonzeroSampler).descriptionSize sizes ≤
      NativeSigning.codeDescription allowance (fun op => sizes.localSize (primitive op))
        (sizes.localSize uniform.request) (sizes.localSize uniform.response)
        (sizes.localSize ports.arity) (sizes.localSize ports.reply)
        (fieldSampler.descriptionSize sizes) (nonzeroSampler.descriptionSize sizes) + 1024 * allowance + 8 := by
  have core := NativeSigning.code_description_of_inputs rep data cost primitive uniform ports
    fieldSampler nonzeroSampler sizes allowance laws dataLaws distribution
  have wrapper : (signing rep data cost primitive uniform ports fieldSampler nonzeroSampler).descriptionSize sizes ≤
      (NativeSigning.code rep data cost primitive uniform ports fieldSampler nonzeroSampler).descriptionSize sizes +
        1024 * allowance + 8 := by
    refine (wrap_description rep data cost primitive keepCacheTy signingInput signingOutput _
      sizes allowance laws dataLaws).trans ?_
    simp only [signingInput, signingOutput, Expression.descriptionBound, Expression.variableDescription]
    omega
  omega

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeComponents
