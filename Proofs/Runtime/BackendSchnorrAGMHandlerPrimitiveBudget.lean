import Proofs.Runtime.BackendSchnorrAGMHandlerComponentBudget

/-! Primitive-derived runtime certificates for the installed common-store
components. No premise assumes the efficiency of a complete handler, adapter
or dispatcher. Indexed request decoding, original-request retention and reply
tagging belong to the surrounding handler and are accounted for separately. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HandlerComponents

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem random_bound (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (width cap basisCap signedCap groupCap rowCap coeffCap arityCap requestTime responseTime drawTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ width)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ width)
    (hrequest : ∀ n ≤ arityCap, Q.cost ports.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost ports.response ⟨n, r⟩ ≤ responseTime)
    (hdraw : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ drawTime) :
    Bounds control queryCost (random rep data cost primitive ports)
      (fun input => Input (Q := Q) rep .nat width cap basisCap signedCap groupCap rowCap coeffCap input ∧ input.1.1 ≤ arityCap)
      (fun output => Output (Q := Q) rep .nat width cap basisCap signedCap output ∧ output.1.1 ≤ arityCap)
      (Random.randomTime overhead width cap basisCap signedCap groupCap rowCap coeffCap requestTime responseTime drawTime +
        2061 * overhead (8192 * frameWidth width cap basisCap signedCap groupCap rowCap coeffCap)) :=
  random_bound_of_native rep data cost primitive sizes lists laws dataLaws mono control queryCost routing ports
    width cap basisCap signedCap groupCap rowCap coeffCap arityCap _ hh hu hb hf hg hn
    (Random.bound rep data cost primitive ports sizes lists laws dataLaws mono control queryCost routing
      width cap basisCap signedCap groupCap rowCap coeffCap arityCap requestTime responseTime drawTime
      hh hu hb hf hg hn hp hr hrequest hresponse hdraw)

variable (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

theorem signing_bound (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width cap basisCap signedCap groupCap rowCap coeffCap fieldTime scaleTime groupTime messageTime pointTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hn : ∀ f : F, (primitiveBound .neg).time f ≤ fieldTime)
    (hs : ∀ f : F, ∀ g : G₁, (primitiveBound .scale₁).time (f, g) ≤ scaleTime)
    (hd : ∀ g h : G₁, (primitiveBound .sub₁).time (g, h) ≤ groupTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (he : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hsample : Bounds control queryCost sampler (fun _ => True) (fun f => Q.size (rep.ty scalar) f ≤ width) sampleTime) :
    Bounds control queryCost (signing rep data cost primitive sampler)
      (Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap)
      (Output (Q := Q) rep scalar width (cap + 1) (basisCap + 1) (signedCap + 1))
      (SigningDispatch.dispatchTime overhead width cap basisCap signedCap groupCap rowCap coeffCap fieldTime scaleTime groupTime
        messageTime pointTime sampleTime +
        2061 * overhead (8192 * frameWidth width cap basisCap signedCap groupCap rowCap coeffCap)) :=
  signing_bound_of_native rep data cost primitive sizes lists laws dataLaws mono control queryCost routing sampler
    width cap basisCap signedCap groupCap rowCap coeffCap _ hh hu hb hf hg
    (SigningDispatch.bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono control queryCost routing
      width cap basisCap signedCap groupCap rowCap coeffCap fieldTime scaleTime groupTime messageTime pointTime sampleTime
      hh hu hb hf hg hz hn hs hd hm he hsample)

theorem hash_bound (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width cap basisCap signedCap groupCap rowCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime pointZeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (he : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hz0 : (primitiveBound .zero₁).time () ≤ pointZeroTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (hmul : ∀ a b : F, (primitiveBound .mul).time (a, b) ≤ mulTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True) (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime) :
    Bounds control queryCost (hash rep data cost primitive sampler)
      (Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap)
      (Output (Q := Q) rep scalar width (cap + 1) basisCap signedCap)
      (HashDispatch.dispatchTime overhead width cap (historyWidth width basisCap signedCap) basisCap groupCap rowCap coeffCap
        comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime sampleTime pointZeroTime +
        2061 * overhead (8192 * frameWidth width cap basisCap signedCap groupCap rowCap coeffCap)) :=
  hash_bound_of_native rep data cost primitive sizes lists laws dataLaws mono control queryCost routing sampler
    width cap basisCap signedCap groupCap rowCap coeffCap _ hh hu hb hf hg
    (HashDispatch.bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono control queryCost routing
      width cap (historyWidth width basisCap signedCap) basisCap groupCap rowCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime pointZeroTime
      hh hu hb hn hf (hg 0) hEq hSub hInc hm he hz hz0 hadd hmul heq hd)

end Signatures.Runtime.SchnorrAGM.Native.HandlerComponents
