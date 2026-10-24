import Proofs.Runtime.BackendSchnorrNonzeroComponents
import Proofs.Runtime.BackendSchnorrROMHandlerComponentBudget

/-! Complete nonzero signing in the shared caller store, derived from original
sampler profiles and primitive costs. Configuration, untouched live cache and
all four successive private-tape states are included in the bound. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeComponents

open BackendProgram RawTape ListROM.NativeComponents

def signingTime (overhead : Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries
      sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime natAddTime
      requestTime responseTime queryTime arityTime replyTime width cap liveCap messageTime pointTime
      scaleTime subTime groupZeroTime scalarAddTime : Nat) : Nat :=
  NativeSigning.runtimeBound overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries
    sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime natAddTime
    requestTime responseTime queryTime arityTime replyTime width cap messageTime pointTime
    scaleTime subTime groupZeroTime scalarAddTime +
      2061 * overhead (8192 * ListROM.NativeComponents.frameWidth width cap liveCap)

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

/-- The core execution budget is proved internally, before adding both executed
adapters and control routing. Only original execution resources are premises. -/
theorem signing_bound
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
      requestTime responseTime queryTime arityTime replyTime width cap liveCap messageTime pointTime
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
    Bounds control queryCost (signing rep data cost primitive uniform ports fieldSampler nonzeroSampler)
      (InputBound (Q := Q) rep message width width tapeWidth cap liveCap savedCap remainingCap)
      (InputBound (Q := Q) rep signatureTy (3 * width) width tapeWidth (cap + 1) liveCap
        (savedCap + 2 * fieldQueries + nonzeroQueries) remainingCap)
      (signingTime overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries
        sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime natAddTime
        requestTime responseTime queryTime arityTime replyTime width cap liveCap messageTime pointTime
        scaleTime subTime groupZeroTime scalarAddTime) := by
  have core := NativeSigning.code_bound rep data cost primitive uniform ports sizes lists laws mono
    control queryCost routing dataLaws primitiveBound distribution fieldSampler nonzeroSampler
    fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth
    savedCap remainingCap counter arityCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime
    queryTime arityTime replyTime width cap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime
    fieldProfile nonzeroProfile tick hh hu hb hz hn hcompare hzero hnatAdd hp hr hrequest hresponse hquery hread hreply
    hsourceTapeWidth hstoreWidth hm hg hscale hsub hgroupZero hgroupZeroTime hscalarAdd
  have htape : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le
      ((savedCap + 2 * fieldQueries + nonzeroQueries + remainingCap) * tapeWidth)]
  exact signing_wrap_bound rep data cost primitive sizes lists laws dataLaws mono control queryCost routing
    (NativeSigning.code rep data cost primitive uniform ports fieldSampler nonzeroSampler)
    width tapeWidth cap liveCap savedCap remainingCap (savedCap + 2 * fieldQueries + nonzeroQueries) _
    (hh.trans htape) hh (hu.trans htape) (by omega) hstoreWidth core

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeComponents
