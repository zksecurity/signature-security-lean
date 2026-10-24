import Proofs.Runtime.BackendSchnorrNonzeroSigningSource
import Proofs.Runtime.BackendSchnorrPrivateSamplingDescription
import Proofs.Runtime.SchnorrROMSharedState

/-! Install the two original sampler programs in the same raw private tape.
The three-draw signing routine retains all sampler queries in their original
families and order. Neither signer draw uses the challenge-family handler. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSigning

open BackendProgram RawTape ListROM

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
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

def code : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env NonzeroSigning.Input) (rep.ty NativeUniform.stateTy))
    (StepClass.HasProd.prod (rep.ty (.pair (.pair point₁ scalar) hashCache)) (rep.ty NativeUniform.stateTy)) :=
  NonzeroSigning.Native.code rep data cost primitive (rep.ty NativeUniform.stateTy)
    (NativePrivate.code rep data cost primitive uniform ports fieldSampler)
    (NativePrivate.code rep data cost primitive uniform ports nonzeroSampler)

/-- Source law for any original scalar-return sampler, including the nonzero
sampler. All internal queries pass through the same saved/remaining tape. -/
theorem sampler_source (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (tape : Shared.Tape F) :
    (NativePrivate.code rep data cost primitive uniform ports sampler).denote ((), tape) =
      Shared.tapeRun (liftRandom (sampler.denote ())) tape :=
  NativePrivate.source rep data cost primitive uniform ports sampler () ⟨tape.1, tape.2⟩

/-- Exact computation equality on every raw tape, including replayed draws.
Only the original samplers' laws are assumed. -/
theorem code_source [SampleableType Fˣ]
    (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
    (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
    (g pk : G₁) (msg : M) (cache : List ((M × G₁) × F)) (tape : Shared.Tape F) :
    (code rep data cost primitive uniform ports fieldSampler nonzeroSampler).denote
      ((msg, g, pk, cache, ()), tape) =
      Shared.tapeRun (liftRandom (NonzeroSigning.source g pk msg cache)) tape := by
  unfold code
  rw [NonzeroSigning.Native.code_denote]
  simp only [sampler_source rep data cost primitive uniform ports, fieldLaw, nonzeroLaw, NonzeroSigning.source,
    _root_.Schnorr.NonzeroNonce.simTranscript, liftRandom, simulateQ_bind, simulateQ_pure,
    simulateQ_map, Shared.tapeRun_bind, Shared.tapeRun_pure, Shared.tapeRun_map,
    bind_map_left, bind_assoc]
  congr 1
  funext first
  congr 1
  funext second
  congr 1
  funext third
  by_cases h : second.1 • g - first.1 • pk = 0 <;>
    simp only [h, ↓reduceIte, simulateQ_pure, Shared.tapeRun_pure, pure_bind,
      NativeCache.programming_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost]

omit [SampleableType F] in
/-- Stored code includes both transformed field-sampler occurrences, the
transformed nonzero sampler and every installed tape-handler occurrence. -/
theorem code_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T),
      sizes.localSize (QD.distribute a b t) ≤ allowance) :
    (code rep data cost primitive uniform ports fieldSampler nonzeroSampler).descriptionSize sizes ≤
      (NativePrivate.handlerDescription rep cost primitive uniform ports sizes allowance + 18 * allowance + 6) *
        (2 * fieldSampler.descriptionSize sizes + nonzeroSampler.descriptionSize sizes) +
      NonzeroSigning.Native.description allowance (fun op => sizes.localSize (primitive op)) := by
  have hf := NativePrivate.description rep data cost primitive uniform ports sizes allowance
    laws dataLaws distribution fieldSampler
  have hn := NativePrivate.description rep data cost primitive uniform ports sizes allowance
    laws dataLaws distribution nonzeroSampler
  have h := NonzeroSigning.Native.code_description rep data cost primitive (rep.ty NativeUniform.stateTy)
    (NativePrivate.code rep data cost primitive uniform ports fieldSampler)
    (NativePrivate.code rep data cost primitive uniform ports nonzeroSampler) sizes allowance laws dataLaws
  exact h.trans (by nlinarith)

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSigning
