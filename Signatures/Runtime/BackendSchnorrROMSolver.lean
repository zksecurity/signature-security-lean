import Signatures.Runtime.BackendSchnorrROMExtraction
import Signatures.Runtime.SchnorrROMListReduction

/-! Complete native general Schnorr ROM solver: initial configuration, actual
retained-tape fork, guarded extraction and uniform fallback. Exact source
correspondence follows from the attacker's measured resources and implementation.
Complete solver resource certificates are separate obligations. -/

open OracleComp OracleSpec PFunctor DiffieHellman
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver

open BackendProgram RawTape NativeInterface NativeComponents

abbrev inputTypes : List (Ty CryptoAtom) := [point₁, point₁]

def initialExpression : Expr CryptoOp inputTypes configTy :=
  .pair (.var .here) (.var (.there .here))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : NativePass.DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def code (fuel qH : Nat) : Code Q unifSpec iface (rep.env inputTypes) (rep.ty scalar) :=
  .seq (.atomic (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression))
    (.seq (NativeROMFork.code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH)
      (NativeExtraction.code rep data cost primitive sampler))

theorem code_denote (fuel qH : Nat) (g pk : G₁) :
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).denote (g, pk, ()) =
      (NativeROMFork.code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).denote
        (g, pk) >>= (NativeExtraction.code rep data cost primitive sampler).denote := by
  simp only [code, Code.denote, pure_bind]
  rfl

variable [SampleableType F] (sample : sampler.denote () = ($ᵗ F : ProbComp F))

include sample in
theorem source_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel qH : Nat) (hfuel : bound.queries ≤ fuel)
    (attacker : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (implementation : R.machine.Implements attacker) (g pk : G₁) :
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).denote (g, pk, ()) =
      simulateQ _root_.Schnorr.LazyROM.sample
        (RawTape.fork ((ListROM.pass (G₂ := G₂) (K := K) (attacker pk)).run ((g, pk), [], []))
          qH (selectPass PrimitiveCosts.unit qH) >>= fun result => liftRandom (extractFork result)) := by
  rw [code_denote, NativeROMFork.source_of_resources rep bd boundary data cost primitive sampler ports uniform
    privatePorts R sample bound hrun fuel qH hfuel attacker implementation, bind_map_left, simulateQ_bind]
  apply bind_congr
  intro result
  rw [NativeExtraction.source rep data cost primitive sampler sample]
  have sample_lift (main : ProbComp F) :
      simulateQ (_root_.Schnorr.LazyROM.sample (F := F)) (liftRandom main) = main := by
    induction main using OracleComp.inductionOn with
    | pure value => simp [liftRandom]
    | query_bind n next ih =>
        simpa only [liftRandom, simulateQ_bind, simulateQ_spec_query,
          _root_.Schnorr.LazyROM.sample, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply] using
          congrArg (fun k : Fin (n + 1) → ProbComp F =>
            (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= k) (funext ih)
  exact (sample_lift _).symm

include sample in
theorem source_reduction [SampleableType G₁] (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel qH : Nat) (hfuel : bound.queries ≤ fuel) (g : G₁)
    (attacker : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (implementation : R.machine.Implements attacker.main) (pk : G₁) :
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).denote (g, pk, ()) =
      _root_.Schnorr.LazyROM.dlogReduction g attacker qH g pk := by
  rw [source_of_resources rep bd boundary data cost primitive sampler ports uniform privatePorts R sample
    bound hrun fuel qH hfuel attacker.main implementation]
  exact congrFun (congrFun (dlogReduction_eq_lazy (G₂ := G₂) (K := K) g attacker qH) g) pk

end Signatures.Runtime.Schnorr.ListROM.NativeSolver
