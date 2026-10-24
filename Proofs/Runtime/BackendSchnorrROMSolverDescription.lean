import Proofs.Runtime.BackendSchnorrROMSolver
import Proofs.Runtime.BackendSchnorrROMForkDescription

/-! Stored-code bounds for the complete general Schnorr ROM solver. Both
fallback sampler occurrences, guarded extraction, setup and every installed
fork component are counted from their actual native implementations. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM

open BackendProgram RawTape NativeInterface NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

namespace NativeExtraction

def descriptionBound : Nat :=
  2 * sampler.descriptionSize sizes + 2 * sizes.localSize (primitive .sub) +
    sizes.localSize (primitive .div) + sizes.localSize (primitive .point₁Eq) +
    sizes.localSize (primitive .scalarEq) + 3 * sizes.localSize (primitive .zero) + 8192 * allowance + 32

include laws dataLaws in
theorem code_description :
    (code rep data cost primitive sampler).descriptionSize sizes ≤
      descriptionBound rep cost primitive sampler sizes allowance := by
  have h := NativeFork.chooseLocal_description rep data cost primitive sizes allowance laws dataLaws expression
  have he : sizes.localSize (NativeFork.chooseLocal rep data cost primitive expression) ≤
      2 * sizes.localSize (primitive .sub) + sizes.localSize (primitive .div) +
        sizes.localSize (primitive .point₁Eq) + sizes.localSize (primitive .scalarEq) +
        3 * sizes.localSize (primitive .zero) + 8188 * allowance := h.trans (by
    simp only [expression, oneExpression, candidateExpression, guardExpression,
      Expression.descriptionBound, Expression.variableDescription]
    omega)
  have hi := laws.identity (rep.ty scalar)
  have hu := dataLaws.unit (rep.ty scalar)
  dsimp only [code, checked, Code.descriptionSize, descriptionBound]
  omega

end NativeExtraction

namespace NativeSolver

variable [C.HasOption] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : NativePass.DataPorts (Q := Q) rep bd)
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

def codeDescription (fuel qH : Nat) : Nat :=
  NativeROMFork.codeDescription rep bd boundary cost primitive sampler ports uniform privatePorts R sizes allowance fuel qH +
    NativeExtraction.descriptionBound rep cost primitive sampler sizes allowance + 64 * allowance + 4

include laws dataLaws dispatchLaws in
theorem code_description (fuel qH : Nat) :
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).descriptionSize sizes ≤
      codeDescription rep cost primitive sampler sizes allowance bd boundary ports uniform privatePorts R fuel qH := by
  have hf := NativeROMFork.code_description rep bd boundary data cost primitive sampler ports uniform privatePorts R
    sizes allowance laws dataLaws dispatchLaws fuel qH
  have he := NativeExtraction.code_description rep data cost primitive sampler sizes allowance laws dataLaws
  have hi := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
    laws dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) initialExpression
  have hs : sizes.localSize
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression) ≤ 64 * allowance :=
    hi.trans (by simp only [initialExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  dsimp only [code, Code.descriptionSize, codeDescription]
  omega

end NativeSolver

end Signatures.Runtime.Schnorr.ListROM
