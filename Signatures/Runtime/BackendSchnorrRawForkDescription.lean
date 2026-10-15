import Signatures.Runtime.BackendSchnorrRawFork

/-! Stored-code accounting for the native fork. Both occurrences of the actual
pass and selector are counted, together with sampling, lookup, reset and every
controller adapter and branch. No tape-size or numeric-position enumeration is
hidden in a controller description. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeFork

open BackendProgram

def adapterDescription (config out : Ty CryptoAtom) (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) : Nat :=
  Expression.descriptionBound allowance primitiveSize (startExpression config) +
  Expression.descriptionBound allowance primitiveSize (firstSelectionExpression config out) +
  Expression.descriptionBound allowance primitiveSize (firstChoiceExpression config out) +
  Expression.descriptionBound allowance primitiveSize (freshExpression config out) +
  Expression.descriptionBound allowance primitiveSize (lookupExpression config out) +
  Expression.descriptionBound allowance primitiveSize (collisionExpression config out) +
  Expression.descriptionBound allowance primitiveSize (resetExpression config out) +
  Expression.descriptionBound allowance primitiveSize (secondExpression config out) +
  Expression.descriptionBound allowance primitiveSize (secondSelectionExpression out) +
  Expression.descriptionBound allowance primitiveSize (finishExpression out)

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
  {iface : Interface (C := C) unifSpec} {config out : Ty CryptoAtom}
  {select : out.Value (cryptoBase F G₁ G₂ K M) → Bool × Nat}
  (selector : Q.Realizer (rep.ty out) (rep.ty choiceTy) select)
  (pass : Code Q unifSpec iface (rep.ty (passInput config)) (rep.ty (passOutput out)))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem compileLocal_description {input output : Ty CryptoAtom} (e : Expr CryptoOp [input] output) :
    sizes.localSize (compileLocal rep data cost primitive e) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) e + 4 * allowance := by
  have framed : sizes.localSize (NativeUniform.frame rep data input) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have compiledSize := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
    laws dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) e
  exact (laws.compose_bound framed compiledSize).trans (by omega)

theorem chooseLocal_description {input output : Ty CryptoAtom}
    (e : Expr CryptoOp [input] (.pair .bool output)) :
    sizes.localSize (chooseLocal rep data cost primitive e) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) e + 6 * allowance :=
  (laws.compose_bound (compileLocal_description rep data cost primitive sizes allowance laws dataLaws e)
    (dataLaws.select (rep.ty output))).trans (by omega)

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem reject_description (input out : Ty CryptoAtom) :
    sizes.localSize (reject rep data input out) ≤
      sizes.localSize (QS.inl rep.data.unit (rep.ty (.pair out out))) + 2 * allowance :=
  (laws.compose_bound (dataLaws.unit (rep.ty input)) (le_refl (sizes.localSize
    (QS.inl rep.data.unit (rep.ty (.pair out out)))))).trans
    (by omega)

omit laws dataLaws in
def descriptionBound : Nat :=
  adapterDescription config out allowance (fun op => sizes.localSize (primitive op)) +
    2 * sizes.localSize selector + 2 * pass.descriptionSize sizes + sampler.descriptionSize sizes +
    NativeLookup.descriptionBound rep cost primitive sizes allowance +
    NativeReset.descriptionBound rep cost primitive sizes allowance +
    3 * sizes.localSize (QS.inl rep.data.unit (rep.ty (.pair out out))) +
    sizes.localSize (QS.inr rep.data.unit (rep.ty (.pair out out))) + 128 * allowance + 128

theorem description :
    (code rep data cost primitive selector pass sampler).descriptionSize sizes ≤
      descriptionBound rep cost primitive selector pass sampler sizes allowance := by
  have hstart := compileLocal_description rep data cost primitive sizes allowance laws dataLaws (startExpression config)
  have hselect₁ := compileLocal_description rep data cost primitive sizes allowance laws dataLaws (firstSelectionExpression config out)
  have hchoice := chooseLocal_description rep data cost primitive sizes allowance laws dataLaws (firstChoiceExpression config out)
  have hfresh := compileLocal_description rep data cost primitive sizes allowance laws dataLaws (freshExpression config out)
  have hlookup := compileLocal_description rep data cost primitive sizes allowance laws dataLaws (lookupExpression config out)
  have hcollision := chooseLocal_description rep data cost primitive sizes allowance laws dataLaws (collisionExpression config out)
  have hreset := compileLocal_description rep data cost primitive sizes allowance laws dataLaws (resetExpression config out)
  have hsecond := compileLocal_description rep data cost primitive sizes allowance laws dataLaws (secondExpression config out)
  have hselect₂ := compileLocal_description rep data cost primitive sizes allowance laws dataLaws (secondSelectionExpression out)
  have hfinish := chooseLocal_description rep data cost primitive sizes allowance laws dataLaws (finishExpression out)
  have hreject₁ := reject_description rep data sizes allowance laws dataLaws (selectedTy config out) out
  have hreject₂ := reject_description rep data sizes allowance laws dataLaws (freshTy config out) out
  have hreject₃ := reject_description rep data sizes allowance laws dataLaws (.pair out out) out
  have hread := NativeLookup.description (iface := iface) rep data cost primitive sizes allowance laws dataLaws
  have hrestarted := NativeReset.description (iface := iface) rep data cost primitive sizes allowance laws dataLaws
  simp only [code, selected, replay, Code.descriptionSize, descriptionBound, adapterDescription]
  omega

end Signatures.Runtime.Schnorr.RawTape.NativeFork
