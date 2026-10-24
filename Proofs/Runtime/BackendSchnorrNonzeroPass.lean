import Proofs.Runtime.BackendSchnorrROMPass
import Proofs.Runtime.BackendSchnorrNonzeroCallerOutput

/-! Exact computation correspondence for the completed native ROM pass. The
singleton wrapper represents a successful return without a default message.
Measured query resources exclude cutoff on every supplied raw tape. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativePass

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativePass

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

/-- The complete pass installs the actual nonzero caller between the unchanged
initialization and final live-cache verification programs. -/
def code (fuel : Nat) : Code Q unifSpec iface (rep.ty inputTy) (rep.ty resultTy) :=
  .seq (setup rep bd boundary data cost primitive)
    (.seq (NativeHandler.caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel)
      (terminal rep bd boundary data cost primitive fieldSampler))

omit [SampleableType F] [SampleableType Fˣ] in
theorem code_denote (fuel : Nat) (tape : Shared.Tape F) (g pk : G₁) :
    (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel).denote (tape, g, pk) =
      (NativeHandler.caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).denote
        (pk, ((g, pk), [], []), tape) >>= fun p =>
          (terminal rep bd boundary data cost primitive fieldSampler).denote p := by
  simp only [code, Code.denote]
  rw [setup_denote, pure_bind]

include fieldLaw nonzeroLaw

theorem source (fuel : Nat)
    (main : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (implementation : R.machine.ImplementsWithin main fuel)
    (tape : Shared.Tape F) (g pk : G₁) :
    (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel).denote (tape, g, pk) =
      (fun p => ([p.1], p.2)) <$>
        Shared.tapeRun ((NonzeroListROM.pass (G₂ := G₂) (K := K) (main pk)).run ((g, pk), [], [])) tape := by
  have hpack : (fun p => ([((p.1), p.2.1)], p.2.2)) <$>
      (Shared.interpret (NonzeroListROM.pass (G₂ := G₂) (K := K) (main pk))).run (((g, pk), [], []), tape) =
      (fun p => ([p.1], p.2)) <$>
        Shared.tapeRun ((NonzeroListROM.pass (G₂ := G₂) (K := K) (main pk)).run ((g, pk), [], [])) tape := by
    simp only [Shared.interpret, StateT.run, Functor.map_map]
  rw [code_denote, NativeHandler.caller_source rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw
    R fuel main implementation, ← hpack]
  simp only [NonzeroListROM.pass, Shared.interpret_bind, StateT.run_bind, map_bind, bind_map_left]
  apply bind_congr
  intro first
  rw [terminal_denote]
  dsimp only
  rw [ListROM.NativeComponents.finalHash_source rep data cost primitive fieldSampler fieldLaw]
  simp only [Shared.interpret_pure, map_pure, bind_pure_comp]

theorem source_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (main : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (implementation : R.machine.Implements main) (tape : Shared.Tape F) (g pk : G₁) :
    (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel).denote (tape, g, pk) =
      (fun p => ([p.1], p.2)) <$>
        Shared.tapeRun ((NonzeroListROM.pass (G₂ := G₂) (K := K) (main pk)).run ((g, pk), [], [])) tape :=
  source rep bd boundary data cost primitive fieldSampler nonzeroSampler fieldLaw nonzeroLaw ports uniform privatePorts R fuel main
    (GeneralCaller.implementsWithin_of_resources R bound hrun main implementation fuel hfuel) tape g pk

theorem completed_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (main : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (implementation : R.machine.Implements main)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (tape : Shared.Tape F) (g pk : G₁)
    (z : Run (resultTy.Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel).run
      control queryCost (tape, g, pk))) : ∃ out, z.value.1 = [out] := by
  have hv := Code.value_mem_denote control queryCost
    (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel) (tape, g, pk) z hz
  rw [source_of_resources rep bd boundary data cost primitive fieldSampler nonzeroSampler fieldLaw nonzeroLaw ports uniform privatePorts R
    bound hrun fuel hfuel main implementation, support_map] at hv
  obtain ⟨p, _, he⟩ := hv
  exact ⟨p.1, (congrArg Prod.fst he).symm⟩

end Signatures.Runtime.Schnorr.NonzeroListROM.NativePass
