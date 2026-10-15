import Signatures.Runtime.BackendSchnorrROMHandler
import Signatures.Runtime.BackendCallerDescription

/-! Complete stored-code accounting for ordinary-ROM dispatch and caller
composition. Bounds count the original sampler, private-tape transformation,
cache kernels, common-store adapters and every request/reply conversion. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram NativeInterface NativeComponents RawTape

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem components_description :
    (NativeComponents.random rep data cost primitive uniform).descriptionSize sizes ≤
      (NativeUniform.code rep data cost primitive uniform).descriptionSize sizes + 1024 * allowance + 8 ∧
    (NativeComponents.hash rep data cost primitive sampler).descriptionSize sizes ≤
      (NativeCache.managed rep data cost primitive (rep.ty NativeUniform.stateTy)
        (NativeDraw.challenge rep data cost primitive sampler)).descriptionSize sizes +
          sizes.localSize (primitive .zero) + 1024 * allowance + 8 ∧
    (NativeComponents.signing rep data cost primitive uniform privatePorts sampler).descriptionSize sizes ≤
      (NativeCache.signing rep data cost primitive (rep.ty NativeUniform.stateTy)
        (NativePrivate.code rep data cost primitive uniform privatePorts sampler)).descriptionSize sizes + 1024 * allowance + 8 ∧
    (NativeComponents.finalHash rep data cost primitive sampler).descriptionSize sizes ≤
      (NativeCache.live rep data cost primitive (rep.ty NativeUniform.stateTy)
        (NativeDraw.challenge rep data cost primitive sampler)).descriptionSize sizes +
          sizes.localSize (primitive .zero) + 1024 * allowance + 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (wrap_description rep data cost primitive cacheStore randomInput randomOutput _ sizes allowance laws dataLaws).trans ?_
    simp only [randomInput, randomOutput, Expression.descriptionBound, Expression.variableDescription]
    omega
  · refine (wrap_description rep data cost primitive configTy hashInput hashOutput _ sizes allowance laws dataLaws).trans ?_
    simp only [hashInput, hashOutput, Expression.descriptionBound, Expression.variableDescription]
    omega
  · refine (wrap_description rep data cost primitive keepCacheTy signingInput signingOutput _ sizes allowance laws dataLaws).trans ?_
    simp only [signingInput, signingOutput, Expression.descriptionBound, Expression.variableDescription]
    omega
  · refine (wrap_description rep data cost primitive keepCacheTy finalInput finalOutput _ sizes allowance laws dataLaws).trans ?_
    simp only [finalInput, finalOutput, Expression.descriptionBound, Expression.variableDescription]
    omega

omit dataLaws QD [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem tagged_description {a b : Ty CryptoAtom}
    {f : (a.Value (cryptoBase F G₁ G₂ K M) × b.Value (cryptoBase F G₁ G₂ K M)) → Response F G₁ M}
    (tag : Q.Realizer (rep.ty (.pair a b)) bd.idx f)
    (body : Code Q unifSpec iface (rep.ty (withStore a)) (rep.ty (withStore b))) :
    (tagged rep bd tag body).descriptionSize sizes ≤ body.descriptionSize sizes + sizes.localSize tag + 18 * allowance + 8 := by
  have hc := Language.withContext_descriptionSize sizes allowance laws (rep.ty storeTy) (Q.identity (rep.ty a)) body
  have hi := laws.identity (rep.ty a)
  have ht : sizes.localSize (Q.compose
      (QP.pair (QP.snd (rep.ty b) (rep.ty a)) (QP.fst (rep.ty b) (rep.ty a))) tag) ≤
      sizes.localSize tag + 4 * allowance :=
    (laws.compose_bound (laws.pair_bound (laws.snd _ _) (laws.fst _ _)) (le_refl _)).trans (by omega)
  dsimp only [tagged, Code.descriptionSize]
  omega

def codeDescription : Nat :=
  NativeUniform.descriptionBound rep cost primitive uniform sizes allowance +
    NativeCache.managedDescription rep cost primitive sizes allowance +
    NativeCache.signingDescription rep cost primitive sizes allowance +
    (NativeChallenge.descriptionBound rep cost primitive sampler sizes allowance + allowance + 2) +
    2 * ((NativePrivate.handlerDescription rep cost primitive uniform privatePorts sizes allowance + 18 * allowance + 6) *
      sampler.descriptionSize sizes) + sizes.localSize (primitive .zero) +
    sizes.localSize ports.request + sizes.localSize ports.randomTag + sizes.localSize ports.hashTag +
    sizes.localSize ports.signingTag + 4096 * allowance + 64

theorem code_description
    (distribute : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T),
      sizes.localSize (QD.distribute a b t) ≤ allowance) :
    (code rep bd ports data cost primitive uniform privatePorts sampler).descriptionSize sizes ≤
      codeDescription rep bd ports cost primitive uniform privatePorts sampler sizes allowance := by
  obtain ⟨hrc, hhc, hsc, _⟩ := components_description rep data cost primitive uniform privatePorts sampler sizes allowance laws dataLaws
  have hr := tagged_description rep bd sizes allowance laws ports.randomTag (NativeComponents.random rep data cost primitive uniform)
  have hh := tagged_description rep bd sizes allowance laws ports.hashTag (NativeComponents.hash rep data cost primitive sampler)
  have hs := tagged_description rep bd sizes allowance laws ports.signingTag (NativeComponents.signing rep data cost primitive uniform privatePorts sampler)
  change (random rep bd ports data cost primitive uniform).descriptionSize sizes ≤ _ at hr
  change (hash rep bd ports data cost primitive sampler).descriptionSize sizes ≤ _ at hh
  change (signing rep bd ports data cost primitive uniform privatePorts sampler).descriptionSize sizes ≤ _ at hs
  have hu := NativeUniform.description rep data cost primitive uniform sizes allowance laws dataLaws
  have hm := NativeCache.managed_description rep data cost primitive (rep.ty NativeUniform.stateTy)
    (NativeDraw.challenge rep data cost primitive sampler) sizes allowance laws dataLaws
  have hsign := NativeCache.signing_description rep data cost primitive (rep.ty NativeUniform.stateTy)
    (NativePrivate.code rep data cost primitive uniform privatePorts sampler) sizes allowance laws dataLaws
  have hd := NativeDraw.challenge_description rep data cost primitive sampler sizes allowance laws dataLaws
  have hp := NativePrivate.description rep data cost primitive uniform privatePorts sizes allowance laws dataLaws distribute sampler
  have hi := distribute rep.data.nat (rep.ty hashKey) (rep.ty storeTy)
  have ho := distribute (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey)) (rep.ty message) (rep.ty storeTy)
  dsimp only [code, dispatch, inner, Code.descriptionSize, codeDescription]
  simp only [positions, NativeInterface.Request, Ty.Value, cryptoBase] at hi ho ⊢
  omega

omit QD in
theorem finalHash_description :
    (NativeComponents.finalHash rep data cost primitive sampler).descriptionSize sizes ≤
      NativeChallenge.descriptionBound rep cost primitive sampler sizes allowance +
        NativeCache.liveDescription rep cost primitive sizes allowance +
        sizes.localSize (primitive .zero) + 1025 * allowance + 10 := by
  have hc : (NativeComponents.finalHash rep data cost primitive sampler).descriptionSize sizes ≤
      (NativeCache.live rep data cost primitive (rep.ty NativeUniform.stateTy)
        (NativeDraw.challenge rep data cost primitive sampler)).descriptionSize sizes +
          sizes.localSize (primitive .zero) + 1024 * allowance + 8 := by
    refine (wrap_description rep data cost primitive keepCacheTy finalInput finalOutput _ sizes allowance laws dataLaws).trans ?_
    simp only [finalInput, finalOutput, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hl := NativeCache.live_description rep data cost primitive (rep.ty NativeUniform.stateTy)
    (NativeDraw.challenge rep data cost primitive sampler) sizes allowance laws dataLaws
  have hd := NativeDraw.challenge_description rep data cost primitive sampler sizes allowance laws dataLaws
  omega

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include dispatchLaws in
theorem caller_description (fuel : Nat) :
    (caller rep bd ports data cost primitive uniform privatePorts sampler R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
        codeDescription rep bd ports cost primitive uniform privatePorts sampler sizes allowance +
        fuel + 55 * allowance + 26 := by
  have hc := Caller.program_descriptionSize_bound R (rep.ty storeTy) sizes allowance laws dispatchLaws
    (code rep bd ports data cost primitive uniform privatePorts sampler) fuel
  have hd := code_description rep bd ports data cost primitive uniform privatePorts sampler sizes allowance laws dataLaws
    dispatchLaws.distribute
  exact hc.trans (by omega)

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
