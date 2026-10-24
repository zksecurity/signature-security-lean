import Proofs.Runtime.BackendSchnorrROMExtractionLocalCost

/-! Derive extraction of one pair from the actual completed-pass encodings
and individual primitive contracts, including intermediate field output sizes. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeExtraction

open BackendProgram

def oneTime (overhead : Nat → Nat) (frame pointTime scalarTime subTime divTime zeroTime : Nat) : Nat :=
  pointTime + scalarTime + 2 * subTime + divTime + zeroTime + 1024 * overhead (512 * frame)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

structure Operations (width pointTime scalarTime subTime divTime zeroTime : Nat) : Prop where
  point : ∀ g h, Q.size (rep.ty point₁) g ≤ 3 * width → Q.size (rep.ty point₁) h ≤ 3 * width →
    (primitiveBound .point₁Eq).time (g, h) ≤ pointTime
  compare : ∀ f g, Q.size (rep.ty scalar) f ≤ 3 * width → Q.size (rep.ty scalar) g ≤ 3 * width →
    (primitiveBound .scalarEq).time (f, g) ≤ scalarTime
  sub : ∀ f g, Q.size (rep.ty scalar) f ≤ 3 * width → Q.size (rep.ty scalar) g ≤ 3 * width →
    Q.size (rep.ty scalar) (f - g) ≤ 3 * width ∧ (primitiveBound .sub).time (f, g) ≤ subTime
  div : ∀ f g, Q.size (rep.ty scalar) f ≤ 3 * width → Q.size (rep.ty scalar) g ≤ 3 * width →
    Q.size (rep.ty scalar) (f / g) ≤ 3 * width ∧ (primitiveBound .div).time (f, g) ≤ divTime
  zero : (primitiveBound .zero).time () ≤ zeroTime

include sizes in
omit [Q.HasCategory] QP QS in
theorem oneValue_scalar (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime : Nat)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (hf : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap first)
    (hs : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap second)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (ops : Operations rep cost primitive primitiveBound width pointTime scalarTime subTime divTime zeroTime) :
    Q.size (rep.ty scalar) (oneValue first second).2 ≤ 3 * width := by
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfz : Q.size (rep.ty scalar) first.1.1.2.2 ≤ width := by
    have h := hf.forged
    simp only [LanguageRepresentation.ty] at *
    grind only
  have hsz : Q.size (rep.ty scalar) second.1.1.2.2 ≤ width := by
    have h := hs.forged
    simp only [LanguageRepresentation.ty] at *
    grind only
  have hd := ops.sub first.1.1.2.2 second.1.1.2.2 (by omega) (by omega)
  have hc := ops.sub first.1.2 second.1.2 hf.challenge hs.challenge
  have hout := (ops.div _ _ hd.1 hc.1).1
  unfold oneValue
  split
  · exact hout
  · exact hz.trans (by omega)

include sizes in
omit [Q.HasCategory] QP QS in
theorem oneValue_size (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime : Nat)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (hf : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap first)
    (hs : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap second)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (ops : Operations rep cost primitive primitiveBound width pointTime scalarTime subTime divTime zeroTime) :
    Q.size (rep.ty resultTy) (oneValue first second) ≤ 5 * width := by
  have hscalar := oneValue_scalar rep cost primitive sizes primitiveBound width managedCap liveCap
    pointTime scalarTime subTime divTime zeroTime first second hf hs hz ops
  have h := sizes.prod_le rep.data.bool (rep.ty scalar) (oneValue first second)
  have hbool := hb (oneValue first second).1
  change Q.size (rep.ty resultTy) _ ≤ _ at h
  omega

include sizes mono

theorem body_time {Γ}
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (acc : Bool × F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width frame managedCap liveCap pointTime scalarTime subTime divTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hw : 8 * width ≤ frame)
    (hi : Q.size (rep.env (bodyTypes Γ)) (second, acc, first, env) ≤ frame)
    (hf : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap first)
    (hs : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap second)
    (ops : Operations rep cost primitive primitiveBound width pointTime scalarTime subTime divTime zeroTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (body (Γ := Γ))).time (second, acc, first, env) ≤
      oneTime overhead frame pointTime scalarTime subTime divTime zeroTime := by
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have fields (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
      (hp : NativePass.CompletedBound (Q := Q) rep width managedCap liveCap p) :
      Q.size (rep.ty point₁) p.1.1.2.1 ≤ width ∧ Q.size (rep.ty scalar) p.1.1.2.2 ≤ width := by
    have h := hp.forged
    simp only [LanguageRepresentation.ty] at *
    grind only
  have hf' := fields first hf
  have hs' := fields second hs
  have hd := ops.sub first.1.1.2.2 second.1.1.2.2 (by omega) (by omega)
  have hc := ops.sub first.1.2 second.1.2 hf.challenge hs.challenge
  have hout := ops.div _ _ hd.1 hc.1
  have hg := guardBody_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    first second acc env frame pointTime scalarTime (by omega) (by omega)
    (fun b => (hb b).trans (by omega)) hi
    (ops.point _ _ (by omega) (by omega)) (ops.compare _ _ hf.challenge hs.challenge)
  have ha := candidateBody_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    first second acc env frame subTime divTime (by omega) hi
    (hd.1.trans (by omega)) (hc.1.trans (by omega)) (hout.1.trans (by omega)) hd.2 hc.2 hout.2
  have h := oneWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (guardBody (Γ := Γ)) candidateBody (second, acc, first, env) frame
    (pointTime + scalarTime + 512 * overhead (256 * frame))
    (2 * subTime + divTime + 256 * overhead (256 * frame)) zeroTime
    (by omega) (by omega) (fun b => (hb b).trans (by omega)) (by omega) hi
    (hout.1.trans (by omega)) hg ha ops.zero
  have hm := mono (show 256 * frame ≤ 512 * frame by omega)
  exact h.trans (by unfold oneTime; omega)

end Signatures.Runtime.Schnorr.ListROM.NativeExtraction
