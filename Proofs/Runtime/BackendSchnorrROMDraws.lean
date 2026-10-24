import Proofs.Runtime.BackendSchnorrRawChallengeBudget
import Proofs.Runtime.BackendSchnorrPrivateSamplingDescription

/-! The two different scalar-draw interfaces used by the ordinary ROM pass.
Hashing records one challenge-family cell. Signing replays the original sampler's
private uniform queries. Challenge sampling does not record those internal queries. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeDraw

open BackendProgram RawTape

def challengeTime (overhead : Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime sampleTime : Nat) : Nat :=
  NativeChallenge.runtimeBound overhead width savedCap remainingCap comparisonTime zeroTime sampleTime +
    3 * overhead (32 * NativeUniform.saveFrameWidth width savedCap remainingCap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

/-- Adapt the existing challenge handler to the cache kernel's stateful-draw
interface. The original sampler runs after challenge tape handling. -/
def challenge : Code Q unifSpec iface
    (StepClass.HasProd.prod rep.data.unit (rep.ty NativeUniform.stateTy))
    (StepClass.HasProd.prod (rep.ty scalar) (rep.ty NativeUniform.stateTy)) :=
  .seq (.atomic (QP.snd rep.data.unit (rep.ty NativeUniform.stateTy)))
    (NativeChallenge.code rep data cost primitive sampler)

theorem challenge_denote (state : State F) :
    (challenge rep data cost primitive sampler).denote ((), NativeUniform.encodeState state) =
      let scan := SeedTape.pop 1 (0, (0 : F), 0) state.remaining
      if scan.1 then pure (scan.2.1.2.1, (state.saved, scan.2.2))
      else (fun answer => (answer, (state.saved ++ [(1, answer, 0)], state.remaining))) <$>
        sampler.denote () := by
  simp only [challenge, Code.denote, pure_bind]
  exact NativeChallenge.denote rep data cost primitive sampler state

theorem challenge_source [SampleableType F] (sample : sampler.denote () = ($ᵗ F : ProbComp F))
    (state : State F) :
    (challenge rep data cost primitive sampler).denote ((), NativeUniform.encodeState state) =
      (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample ((oracle (.inr ())).run state) := by
  simp only [challenge, Code.denote, pure_bind]
  exact NativeChallenge.source rep data cost primitive sampler sample state

theorem challenge_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (challenge rep data cost primitive sampler).descriptionSize sizes ≤
      NativeChallenge.descriptionBound rep cost primitive sampler sizes allowance + allowance + 2 := by
  have hc := NativeChallenge.description rep data cost primitive sampler sizes allowance laws dataLaws
  have hs := laws.snd rep.data.unit (rep.ty NativeUniform.stateTy)
  dsimp only [challenge, Code.descriptionSize]
  omega

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem challenge_bound (width savedCap remainingCap comparisonTime zeroTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hcompare : ∀ n, Q.size rep.data.nat n ≤ width → (primitiveBound .natEq).time (n, 1) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hsample : Bounds control queryCost sampler (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) sampleTime) :
    Bounds control queryCost (challenge rep data cost primitive sampler)
      (fun p => NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap p.2)
      (NativeChallenge.Output (Q := Q) rep width (savedCap + 1) remainingCap)
      (challengeTime overhead width savedCap remainingCap comparisonTime zeroTime sampleTime) := by
  let W := NativeUniform.saveFrameWidth width savedCap remainingCap
  let fee := overhead (32 * W)
  let inv := NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap
  have hw : width ≤ W := by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith
  have hstate (s) (hs : inv s) : Q.size (rep.ty NativeUniform.stateTy) s ≤ W :=
    (NativeUniform.state_size rep sizes lists width savedCap remainingCap hh s hs).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have hinput (p : Unit × NativeUniform.stateTy.Value (cryptoBase F G₁ G₂ K M)) (hp : inv p.2) :
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty NativeUniform.stateTy)) p ≤ 3 * W := by
    have hs := hstate p.2 hp
    have h := sizes.prod_le rep.data.unit (rep.ty NativeUniform.stateTy) p
    have hun : Q.size rep.data.unit p.1 ≤ width := by
      simpa only [Subsingleton.elim p.1 ()] using hu
    omega
  have hproject : Bounds control queryCost
      (.atomic (iface := iface) (QP.snd rep.data.unit (rep.ty NativeUniform.stateTy)))
      (fun p => inv p.2) inv (2 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hs := hstate input.2 hi
    have hin := hinput input hi
    have ht := (laws.snd rep.data.unit (rep.ty NativeUniform.stateTy) input).trans (mono (show
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty NativeUniform.stateTy)) input +
        Q.size (rep.ty NativeUniform.stateTy) input.2 ≤ 32 * W by omega))
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty NativeUniform.stateTy)) input +
        Q.size (rep.ty NativeUniform.stateTy) input.2 ≤ 32 * W by omega))
    exact ⟨hi, by dsimp only [fee]; omega⟩
  have hdraw := NativeChallenge.bound rep data cost primitive sampler sizes lists laws dataLaws
    primitiveBound mono control queryCost routing width savedCap remainingCap comparisonTime zeroTime sampleTime
    hh hu hb hz hn0 hn1 hcompare hzero hsample
  have hall := Bounds.seq control queryCost
    (.atomic (QP.snd rep.data.unit (rep.ty NativeUniform.stateTy)))
    (NativeChallenge.code rep data cost primitive sampler)
    (fun p => inv p.2) inv _ (2 * fee) _ fee hproject hdraw (by
    intro input hi s hs
    have hin := hinput input hi
    have hout := hstate s hs
    exact (routing.sequence _ _).trans (mono (by omega)))
  intro input hi z hz'
  obtain ⟨ho, ht⟩ := hall input hi z hz'
  exact ⟨ho, ht.trans (by dsimp only [challengeTime, fee, W] at *; omega)⟩

omit sizes lists laws dataLaws mono routing in
theorem challengeTime_polynomial (overhead : Nat → Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime sampleTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hSaved : PolynomiallyBounded savedCap) (hRemaining : PolynomiallyBounded remainingCap)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hSample : PolynomiallyBounded sampleTime) :
    PolynomiallyBounded (fun n => challengeTime (overhead n) (width n) (savedCap n) (remainingCap n)
      (comparisonTime n) (zeroTime n) (sampleTime n)) := by
  have h := NativeChallenge.runtimeBound_polynomial overhead width savedCap remainingCap comparisonTime zeroTime
    sampleTime hOverhead hWidth hSaved hRemaining hCompare hZero hSample
  unfold challengeTime NativeUniform.saveFrameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.ListROM.NativeDraw
