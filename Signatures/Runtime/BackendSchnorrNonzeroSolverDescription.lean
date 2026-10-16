import Signatures.Runtime.BackendSchnorrNonzeroSolver
import Signatures.Runtime.BackendSchnorrNonzeroForkDescription
import Signatures.Runtime.BackendSchnorrROMSolverDescription

/-! Stored-code bounds for the complete general Schnorr ROM solver. Both
fallback sampler occurrences, guarded extraction, setup and every installed
fork component are counted from their actual native implementations. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeSolver

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
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

namespace NativeSolver

variable [C.HasOption] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : ListROM.NativePass.DataPorts (Q := Q) rep bd)
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

def codeDescription (fuel qH : Nat) : Nat :=
  NativeROMFork.codeDescription rep bd boundary cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R sizes allowance fuel qH +
    NativeExtraction.descriptionBound rep cost primitive fieldSampler sizes allowance + 64 * allowance + 4

include laws dataLaws dispatchLaws in
theorem code_description (fuel qH : Nat) :
    (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel qH).descriptionSize sizes ≤
      codeDescription rep cost primitive fieldSampler nonzeroSampler sizes allowance bd boundary ports uniform privatePorts R fuel qH := by
  have hf := NativeROMFork.code_description rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R
    sizes allowance laws dataLaws dispatchLaws fuel qH
  have he := NativeExtraction.code_description rep data cost primitive fieldSampler sizes allowance laws dataLaws
  have hi := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
    laws dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) initialExpression
  have hs : sizes.localSize
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression) ≤ 64 * allowance :=
    hi.trans (by simp only [initialExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  dsimp only [code, Code.descriptionSize, codeDescription]
  omega

end NativeSolver

end Signatures.Runtime.Schnorr.NonzeroListROM
