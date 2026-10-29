import Proofs.Runtime.BackendWeightedTermsCost

/-! Complete native term generators, with source semantics, runtime bounds,
and stored-code bounds. These are components of the weighted reductions;
this module does not yet certify the complete composed solver. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Terms

open Weights BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

/-- The semantic index is the actual OOPS source term list. -/
def oopsCode (d : Nat) : Q.Realizer (rep.env [oopsMessage]) (rep.ty (.list (termTy (oopsKey d))))
    (fun env => OOPS.LazyAGM.terms d env.1) :=
  (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (oops d)).castFunction (by
    funext env
    simpa only [Expr.run_value] using
      oops_value (G₁ := G₁) (G₂ := G₂) (M := M) cost d env.1)

/-- Proximity's source indices are encoded by the established bijection. -/
def proximityCode (ell : Nat) :
    Q.Realizer (rep.env [proximityTupleMessage ell]) (rep.ty (.list (termTy (proximityKey ell))))
      (fun env => (Proximity.LazyAGM.terms (proximityMessageEquiv ell env.1)).map
        (Prod.map encodeProximityKey id)) :=
  (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (proximity ell)).castFunction (by
    funext env
    simpa only [Expr.run_value] using
      proximity_value (G₁ := G₁) (G₂ := G₂) (M := M) cost ell env.1)

/-- The semantic index is the synchronized PS source term list. -/
def syncCode (weighted : Bool) : Q.Realizer (rep.env [syncMessage]) (rep.ty (.list (termTy key)))
    (fun env => syncTerms weighted env.1) :=
  (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (sync weighted)).castFunction (by
    funext env
    simpa only [Expr.run_value] using
      sync_value (G₁ := G₁) (G₂ := G₂) (M := M) cost weighted env.1)

section Description

variable (descriptions : DescriptionSize Q) (allowance : Nat)
  (descriptionLaws : LocalDescriptionLaws descriptions allowance)
  (descriptionData : DataDescriptionLaws descriptions rep.data data allowance)
  (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
  (hp : ∀ {a b} (instr : CryptoOp a b), descriptions.localSize (primitive instr) ≤ primitiveSize instr)

include descriptionLaws descriptionData hp

theorem oopsCode_size (d : Nat) :
    descriptions.localSize (oopsCode rep data cost primitive d) ≤ oopsDescription allowance primitiveSize d := by
  rw [oopsCode, DescriptionSize.castFunction]
  exact (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive descriptions
    allowance descriptionLaws descriptionData primitiveSize hp (oops d)).trans
      (oops_description allowance primitiveSize d)

theorem proximityCode_size (ell : Nat) :
    descriptions.localSize (proximityCode rep data cost primitive ell) ≤
      proximityDescription allowance primitiveSize ell := by
  rw [proximityCode, DescriptionSize.castFunction]
  exact (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive descriptions
    allowance descriptionLaws descriptionData primitiveSize hp (proximity ell)).trans
      (proximity_description allowance primitiveSize ell)

theorem syncCode_size (weighted : Bool) :
    descriptions.localSize (syncCode rep data cost primitive weighted) ≤
      syncDescription allowance primitiveSize := by
  rw [syncCode, DescriptionSize.castFunction]
  exact (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive descriptions
    allowance descriptionLaws descriptionData primitiveSize hp (sync weighted)).trans
      (sync_description allowance primitiveSize weighted)

end Description

def termSpace (width n : Nat) : Nat := (6 * n + 1) * width

def termFee (overhead : Nat → Nat) (width n : Nat) : Nat :=
  overhead (128 * (termSpace width n + width))

def oopsNativeTime (overhead : Nat → Nat) (width d indexTime mulTime oneTime : Nat) : Nat :=
  (d + 1) * (indexTime + mulTime + 64 * termFee overhead width (d + 1)) +
    oneTime + 68 * termFee overhead width (d + 1)

def proximityNativeTime (overhead : Nat → Nat) (width ell indexTime zeroTime oneTime : Nat) : Nat :=
  ell * (indexTime + 64 * termFee overhead width ell) +
    zeroTime + oneTime + 68 * termFee overhead width ell

def syncNativeTime (overhead : Nat → Nat) (width oneTime : Nat) : Nat :=
  oneTime + 64 * termFee overhead width 1

section Cost

variable [C.HasOption]
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include laws dataLaws sizes lists mono

theorem syncCode_cost (weighted : Bool) (m : K × F) (width oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) m.1 ≤ width)
    (h1 : (primitiveBound .one).time () ≤ oneTime) :
    Q.cost (syncCode rep data cost primitive weighted) (m, ()) ≤ syncNativeTime overhead width oneTime := by
  rw [syncCode, QuantitativeStepClass.Realizer.cost_castFunction]
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (sync weighted) (m, ())).trans ?_
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty (termTy key))
  have hcons := @lists.cons_le
  have hone := hf 1
  have hmessage := hf m.2
  have hfee : ∀ k ≤ 128 * (termSpace width 1 + width), overhead k ≤ termFee overhead width 1 :=
    fun _ h => mono h
  cases weighted <;>
    dsimp only [sync, Expression.compileBound, Expression.variableBound, LocalBound.compose,
      LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity, DataCostLaws.unitBound,
      DataCostLaws.nilBound, DataCostLaws.consBound, Expr.denote, Var.get, arithmetic, termTy,
      syncNativeTime, termFee, termSpace, LanguageRepresentation.ty, LanguageRepresentation.env] at * <;>
    grind only

theorem oopsCode_cost (d : Nat) (mt : F × K) (width indexTime mulTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) mt.2 ≤ width)
    (hj : ∀ j : Fin (d + 1), Q.size (rep.ty (boundedNat d)) j ≤ width)
    (hn : ∀ k ≤ d + 1, Q.size rep.data.nat k ≤ width)
    (hi : ∀ k ≤ d + 1, (primitiveBound (.finOfNat d)).time k ≤ indexTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime) :
    Q.cost (oopsCode rep data cost primitive d) (mt, ()) ≤
      oopsNativeTime overhead width d indexTime mulTime oneTime := by
  rw [oopsCode, QuantitativeStepClass.Realizer.cost_castFunction]
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (oops d) (mt, ())).trans ?_
  have hrec := oopsFrom_native_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    d (d + 1) 0 1 mt (Γ := []) () width (termSpace width (d + 1)) indexTime mulTime
    hh hu hf hk hj (by simpa using hn)
    (by dsimp [LanguageRepresentation.env, termSpace]; nlinarith) (by simpa using hi) hm
  have hout := oops_output_size rep sizes lists cost d mt width hh hf hk hj
  change _ ≤ termSpace width (d + 1) at hout
  have hwidth : width ≤ termSpace width (d + 1) := by dsimp [termSpace]; nlinarith
  have hp := @sizes.prod_le
  have hscalar := hf 1
  have hmessage := hf mt.1
  have hone : (arithmetic F G₁ G₂ K M cost).execute .one () = (1 : F) := rfl
  have hfee : ∀ k ≤ 128 * (termSpace width (d + 1) + width),
      overhead k ≤ termFee overhead width (d + 1) := fun _ h => mono h
  have hstep :
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (oops d)).time (mt, ()) ≤
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (oopsFrom d (d + 1) 0 (Γ := []))).time (1, mt, ()) +
          oneTime + 64 * termFee overhead width (d + 1) := by
    clear hrec
    simp only [oops, Expression.compileBound, LocalBound.compose, LocalBound.pair, LocalBound.identity,
      DataCostLaws.unitBound, Expr.denote, hone,
      LanguageRepresentation.ty, LanguageRepresentation.env, termFee] at *
    grind only
  dsimp only [oopsNativeTime, termFee] at *
  nlinarith

theorem proximityCode_cost (ell : Nat)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M))
    (width indexTime zeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hv : Q.size (rep.ty (tupleTy scalar ell)) ms.1 ≤ width)
    (hk : Q.size (rep.ty key) ms.2 ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width)
    (hn : ∀ k ≤ ell + 1, Q.size rep.data.nat k ≤ width)
    (hi : ∀ k ≤ ell + 1, (primitiveBound (.finOfNat ell)).time k ≤ indexTime)
    (h0 : (primitiveBound (.finZero ell)).time () ≤ zeroTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime) :
    Q.cost (proximityCode rep data cost primitive ell) (ms, ()) ≤
      proximityNativeTime overhead width ell indexTime zeroTime oneTime := by
  rw [proximityCode, QuantitativeStepClass.Realizer.cost_castFunction]
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (proximity ell) (ms, ())).trans ?_
  have hrec := proximityFrom_native_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    ell ell 1 ms (Γ := []) () width (termSpace width ell) indexTime
    hh hu hf hv hk hj (by intro k hk; exact hn k (by omega))
    (by dsimp [LanguageRepresentation.env, termSpace]; nlinarith)
    (by intro k hk; exact hi k (by omega))
  have hout := proximity_output_size rep sizes lists cost ell ms width hh hf hk hj
  have htail := proximityFrom_output_size rep sizes lists cost ell ell 1 ms (Γ := []) () width hh hf hk hj
  have hlength : (6 * (ell + 1) + 1) * width = termSpace width ell + 6 * width := by
    dsimp [termSpace]
    ring
  rw [hlength] at hout
  change _ ≤ termSpace width ell at htail
  have hwidth : width ≤ termSpace width ell := by dsimp [termSpace]; nlinarith
  have hp := @sizes.prod_le
  have hc := @lists.cons_le
  have hscalar := hf 1
  have htag := hj 0
  have hone : (arithmetic F G₁ G₂ K M cost).execute .one () = (1 : F) := rfl
  have hzero : (arithmetic F G₁ G₂ K M cost).execute (.finZero ell) () = (0 : Fin (ell + 1)) := rfl
  have hfee : ∀ k ≤ 128 * (termSpace width ell + width),
      overhead k ≤ termFee overhead width ell := fun _ h => mono h
  have hstep :
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (proximity ell)).time (ms, ()) ≤
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (proximityFrom ell ell 1 (Γ := []))).time (ms, ()) +
          zeroTime + oneTime + 64 * termFee overhead width ell := by
    clear hrec
    simp only [proximity, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
      DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Var.get, hone, hzero]
    generalize hrows : (proximityFrom ell ell 1 (Γ := [])).denote
      (arithmetic F G₁ G₂ K M cost) (ms, ()) = rows at htail hout ⊢
    dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, termFee] at *
    grind only
  dsimp only [proximityNativeTime, termFee] at *
  nlinarith

/-- The full tuple width is derived from coordinate encodings. The resulting
budget charges the numerical dimension even when all individual scalars are small. -/
theorem proximityCode_cost_of_atoms (ell : Nat)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M))
    (width indexTime zeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) ms.2 ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width)
    (hn : ∀ k ≤ ell + 1, Q.size rep.data.nat k ≤ width)
    (hi : ∀ k ≤ ell + 1, (primitiveBound (.finOfNat ell)).time k ≤ indexTime)
    (h0 : (primitiveBound (.finZero ell)).time () ≤ zeroTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime) :
    Q.cost (proximityCode rep data cost primitive ell) (ms, ()) ≤
      proximityNativeTime overhead ((2 * ell + 1) * width) ell indexTime zeroTime oneTime := by
  have hw : width ≤ (2 * ell + 1) * width := by nlinarith
  exact proximityCode_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    ell ms ((2 * ell + 1) * width) indexTime zeroTime oneTime (hh.trans hw) (hu.trans hw)
    (fun x => (hf x).trans hw) (tuple_size rep sizes scalar ell ms.1 width hh hu hf)
    (hk.trans hw) (fun j => (hj j).trans hw) (fun k hk => (hn k hk).trans hw) hi h0 h1

end Cost

end Signatures.Runtime.WeightedAGM.Terms
