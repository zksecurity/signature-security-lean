import Signatures.Runtime.BackendSchnorrNonzeroPrivateSigning
import Signatures.Runtime.BackendSchnorrNonzeroSigningBudget
import Signatures.Runtime.BackendSchnorrPrivateSamplingResources

/-! Complete runtime of the three-draw signer after installing both original
samplers in the raw private tape. Original work, visits and queries are separate
for the two sampler programs. Every replay traversal and growing tape is charged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSigning

open BackendProgram RawTape ListROM.NativeCache

/-- Evaluate the derived private-sampler budget at the actual successive tape
capacities, then add the complete signing wrapper's arithmetic/cache costs. -/
def runtimeBound (overhead : Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries
      sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime natAddTime
      requestTime responseTime queryTime arityTime replyTime width cap messageTime pointTime
      scaleTime subTime groupZeroTime scalarAddTime : Nat) : Nat :=
  let first := NativePrivate.samplerTime overhead fieldWork fieldVisits fieldQueries sourceWidth tapeWidth
    savedCap remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
  let second := NativePrivate.samplerTime overhead fieldWork fieldVisits fieldQueries sourceWidth tapeWidth
    (savedCap + fieldQueries) remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
  let third := NativePrivate.samplerTime overhead nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth
    (savedCap + 2 * fieldQueries) remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
  NonzeroSigning.Native.signingTime overhead width cap messageTime pointTime scaleTime subTime
    groupZeroTime scalarAddTime first second third

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws mono routing

/-- Derive the actual installed signer's runtime, scalar sizes and tape growth
from the two original execution profiles. No transformed-component budget is a
premise, and numerical arities/counters need not have polynomial magnitude. -/
theorem code_bound
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
    (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T) (p : (A ⊕ B) × T),
      Q.cost (QD.distribute a b t) p ≤ overhead
        (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) t) p +
          Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a t) (StepClass.HasProd.prod b t))
            (StateSimulation.distributeValue p)))
    (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries
      sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime comparisonTime zeroTime natAddTime
      requestTime responseTime queryTime arityTime replyTime width cap messageTime pointTime
      scaleTime subTime groupZeroTime scalarAddTime : Nat)
    (fieldProfile : ExecutionProfile.Within fieldSampler () fieldWork fieldVisits fieldQueries
      sourceWidth counter (fun n => n ≤ arityCap))
    (nonzeroProfile : ExecutionProfile.Within nonzeroSampler () nonzeroWork nonzeroVisits nonzeroQueries
      sourceWidth counter (fun n => n ≤ arityCap))
    (tick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
      (savedCap + 2 * fieldQueries) remainingCap nonzeroQueries, control.loop n size ≤ tickTime)
    (hh : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ tapeWidth)
    (hb : ∀ b, Q.size rep.data.bool b ≤ tapeWidth) (hz : Q.size (rep.ty scalar) (0 : F) ≤ tapeWidth)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ tapeWidth)
    (hcompare : ∀ a b, Q.size rep.data.nat a ≤ tapeWidth → Q.size rep.data.nat b ≤ tapeWidth →
      (primitiveBound .natEq).time (a, b) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hnatAdd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ natAddTime)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ tapeWidth)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ tapeWidth)
    (hrequest : ∀ n ≤ arityCap, Q.cost uniform.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost uniform.response ⟨n, r⟩ ≤ responseTime)
    (hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime)
    (hread : ∀ n ≤ arityCap, Q.cost ports.arity n ≤ arityTime)
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ tapeWidth → Q.cost ports.reply (r, n) ≤ replyTime)
    (hsourceTapeWidth : sourceWidth ≤ tapeWidth)
    (hstoreWidth : (6 * (savedCap + 2 * fieldQueries + nonzeroQueries + remainingCap) + 3) * tapeWidth ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
      Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
      Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime)
    (hgroupZero : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hgroupZeroTime : (primitiveBound .zero₁).time () ≤ groupZeroTime)
    (hscalarAdd : ∀ z a : F, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty scalar) a ≤ width →
      Q.size (rep.ty scalar) (z + a) ≤ width ∧ (primitiveBound .add).time (z, a) ≤ scalarAddTime) :
    Bounds control queryCost (code rep data cost primitive uniform ports fieldSampler nonzeroSampler)
      (fun p => SigningInput (Q := Q) rep width cap p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap p.2)
      (fun p => SigningOutput (Q := Q) rep width (cap + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth
          (savedCap + 2 * fieldQueries + nonzeroQueries) remainingCap p.2)
      (runtimeBound overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries
        sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime natAddTime
        requestTime responseTime queryTime arityTime replyTime width cap messageTime pointTime
        scaleTime subTime groupZeroTime scalarAddTime) := by
  let inv := fun cap => NativeUniform.StateBound (Q := Q) rep tapeWidth cap remainingCap
  let drawTime := fun work visits queries cap => NativePrivate.samplerTime overhead work visits queries
    sourceWidth tapeWidth cap remainingCap tickTime comparisonTime zeroTime natAddTime
    requestTime responseTime queryTime arityTime replyTime
  have htape : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le
      ((savedCap + 2 * fieldQueries + nonzeroQueries + remainingCap) * tapeWidth)]
  have hsourceWidth := hsourceTapeWidth.trans htape
  have hdraw (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
      (work visits queries cap : Nat)
      (profile : ExecutionProfile.Within sampler () work visits queries sourceWidth counter (fun n => n ≤ arityCap))
      (hcap : cap + queries ≤ savedCap + 2 * fieldQueries + nonzeroQueries) :
      Bounds control queryCost (NativePrivate.code rep data cost primitive uniform ports sampler)
        (fun p => inv cap p.2)
        (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ inv (cap + queries) p.2)
        (drawTime work visits queries cap) := by
    have htick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth cap remainingCap queries,
        control.loop n size ≤ tickTime := by
      intro n hn' size hs
      apply tick n hn' size
      unfold NativePrivate.samplerWidth NativePrivate.frameWidth at hs ⊢
      nlinarith only [hs, Nat.mul_le_mul_right tapeWidth hcap]
    have hd := NativePrivate.sampler_bound rep data cost primitive uniform ports sizes lists laws mono
      control queryCost routing dataLaws primitiveBound distribution sampler (fun _ => True)
      work visits queries sourceWidth tapeWidth cap remainingCap counter arityCap tickTime
      comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
      (by intro input _; cases input; exact profile) htick hh hu hb hz hn hcompare hzero hnatAdd hp hr
      hrequest hresponse hquery hread hreply
    intro input hi z hz'
    obtain ⟨ho, ht⟩ := hd input ⟨True.intro, hi⟩ z hz'
    exact ⟨⟨ho.1.trans hsourceWidth, ho.2⟩, ht⟩
  have hstore (cap : Nat) (hcap : cap ≤ savedCap + 2 * fieldQueries + nonzeroQueries)
      (saved) (hs : inv cap saved) : Q.size (rep.ty NativeUniform.stateTy) saved ≤ width := by
    have h := NativeUniform.state_size rep sizes lists tapeWidth cap remainingCap hh saved hs
    apply h.trans
    nlinarith only [hstoreWidth, Nat.mul_le_mul_right tapeWidth hcap]
  have first := hdraw fieldSampler fieldWork fieldVisits fieldQueries savedCap fieldProfile (by omega)
  have second : Bounds control queryCost (NativePrivate.code rep data cost primitive uniform ports fieldSampler)
      (fun p => inv (savedCap + fieldQueries) p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ inv (savedCap + 2 * fieldQueries) p.2)
      (drawTime fieldWork fieldVisits fieldQueries (savedCap + fieldQueries)) := by
    simpa only [two_mul, Nat.add_assoc] using
      hdraw fieldSampler fieldWork fieldVisits fieldQueries (savedCap + fieldQueries) fieldProfile (by omega)
  have third := hdraw nonzeroSampler nonzeroWork nonzeroVisits nonzeroQueries
    (savedCap + 2 * fieldQueries) nonzeroProfile le_rfl
  exact NonzeroSigning.Native.code_bound rep data cost primitive (rep.ty NativeUniform.stateTy)
    (NativePrivate.code rep data cost primitive uniform ports fieldSampler)
    (NativePrivate.code rep data cost primitive uniform ports nonzeroSampler)
    sizes lists laws dataLaws primitiveBound mono control queryCost routing
    (inv savedCap) (inv (savedCap + fieldQueries)) (inv (savedCap + 2 * fieldQueries))
    (inv (savedCap + 2 * fieldQueries + nonzeroQueries)) width cap messageTime pointTime scaleTime subTime
    groupZeroTime scalarAddTime (drawTime fieldWork fieldVisits fieldQueries savedCap)
    (drawTime fieldWork fieldVisits fieldQueries (savedCap + fieldQueries))
    (drawTime nonzeroWork nonzeroVisits nonzeroQueries (savedCap + 2 * fieldQueries))
    (hh.trans htape) (hu.trans htape) (fun b => (hb b).trans htape)
    (hstore savedCap (by omega)) (hstore (savedCap + fieldQueries) (by omega))
    (hstore (savedCap + 2 * fieldQueries) (by omega))
    (hstore (savedCap + 2 * fieldQueries + nonzeroQueries) le_rfl)
    hm hg hscale hsub hgroupZero hgroupZeroTime hscalarAdd first second third

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSigning
