import Signatures.Runtime.BackendLanguageCorrectness
import Signatures.Runtime.Machine

/-! Compile the existing cryptographic wrapper machine to the common backend.

Field/group instructions and primitive sampling retain individual executable
implementation contracts. Reads, writes, local expressions, argument frames, and
control flow are constructed here. No hash/sign oracle or complete reduction is
introduced as a primitive. Correctness preserves the original joint effect law.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.MachineCompiler

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [QP : Q.HasProd]
  {F G₁ G₂ K M : Type} [SampleableType F]
  {iface : Interface (C := C) unifSpec}

/-- Sampling is an effect implementation, independent of the source caller.
Efficiency still requires bounds for this code and its encodings. -/
structure SamplingImplementation (Q : QuantitativeStepClass.{0, v, w} C)
    (iface : Interface (C := C) unifSpec)
    (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)) where
  scalar : Code Q unifSpec iface rep.data.unit (rep.ty Runtime.scalar)
  uniform : (n : Nat) → Code Q unifSpec iface rep.data.unit (rep.ty (boundedNat n))
  scalar_denote : ∀ input, scalar.denote input = ($ᵗ F : ProbComp F)
  uniform_denote : ∀ n input, (uniform n).denote input = (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))

variable (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (samplingCode : SamplingImplementation Q iface rep)

def effects (store : Ty CryptoAtom) {a b} (instr : Machine.Effect store a b) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty store))
      (StepClass.HasProd.prod (rep.ty b) (rep.ty store)) :=
  match instr with
  | .scalar => .first (rep.ty store) samplingCode.scalar
  | .uniform n => .first (rep.ty store) (samplingCode.uniform n)
  | .read => .atomic (QP.pair (QP.snd _ _) (QP.snd _ _))
  | .write => .atomic (QP.pair (data.unit _) (QP.fst _ _))

theorem effects_denote (sampling : Machine.SamplingCosts) (store : Ty CryptoAtom)
    {a b} (instr : Machine.Effect store a b)
    (input : a.Value (cryptoBase F G₁ G₂ K M))
    (saved : store.Value (cryptoBase F G₁ G₂ K M)) :
    (effects rep data samplingCode store instr).denote (input, saved) =
      (fun p => (p.1.value, p.2)) <$>
        (Machine.effects sampling store instr input).run saved := by
  cases instr <;>
    simp [effects, Code.denote, samplingCode.scalar_denote, samplingCode.uniform_denote,
      Machine.effects, StateT.run, Functor.map_map]

theorem effects_denote_state (sampling : Machine.SamplingCosts) (store : Ty CryptoAtom)
    {a b} (instr : Machine.Effect store a b)
    (input : a.Value (cryptoBase F G₁ G₂ K M))
    (saved : store.Value (cryptoBase F G₁ G₂ K M)) :
    (effects rep data samplingCode store instr).denote (input, saved) =
      (Run.value <$> Machine.effects sampling store instr input).run saved := by
  simpa only [StateT.run_map, Prod.map] using
    effects_denote rep data samplingCode sampling store instr input saved

variable [Q.HasCategory] [QS : Q.HasSum] [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def program (store : Ty CryptoAtom) {Γ a} (source : Program CryptoOp (Machine.Effect store) Γ a) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.env Γ) (rep.ty store))
      (StepClass.HasProd.prod (rep.ty a) (rep.ty store)) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (rep.ty store)
    (effects rep data samplingCode store) source

theorem program_denote (sampling : Machine.SamplingCosts) (store : Ty CryptoAtom)
    {Γ a} (source : Program CryptoOp (Machine.Effect store) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (saved : store.Value (cryptoBase F G₁ G₂ K M)) :
    (program rep data samplingCode cost primitive store source).denote (env, saved) =
      (fun p => (p.1.value, p.2)) <$>
        (source.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) env).run saved := by
  rw [program, Language.compile_denote rep data (arithmetic F G₁ G₂ K M cost) primitive
    (rep.ty store) (effects rep data samplingCode store)
    (fun instr input => Run.value <$> Machine.effects sampling store instr input)
    (effects_denote_state rep data samplingCode sampling store)]
  simpa only [StateT.run_map, Prod.map] using (congrArg (fun c => c.run saved)
    (Program.run_erase (m := StateT (store.Value (cryptoBase F G₁ G₂ K M)) ProbComp)
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) source env)).symm

/-- Construct the argument frame for a unary wrapper routine. -/
def unary (store : Ty CryptoAtom) {a b}
    (source : Program CryptoOp (Machine.Effect store) [a] b) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty store))
      (StepClass.HasProd.prod (rep.ty b) (rep.ty store)) :=
  .seq (.atomic (QP.pair (QP.pair (QP.fst _ _) (data.unit _)) (QP.snd _ _)))
    (program rep data samplingCode cost primitive store source)

theorem unary_denote (sampling : Machine.SamplingCosts) (store : Ty CryptoAtom)
    {a b} (source : Program CryptoOp (Machine.Effect store) [a] b)
    (input : a.Value (cryptoBase F G₁ G₂ K M)) (saved : store.Value (cryptoBase F G₁ G₂ K M)) :
    (unary rep data samplingCode cost primitive store source).denote (input, saved) =
      (fun p => (p.1.value, p.2)) <$>
        (source.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) (input, ())).run saved := by
  simp only [unary, Code.denote, pure_bind]
  exact program_denote rep data samplingCode cost primitive sampling store source (input, ()) saved

def closed {Γ a} (source : Machine.Code Γ a) : Code Q unifSpec iface (rep.env Γ) (rep.ty a) :=
  .seq (.atomic (QP.pair (Q.identity _)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive source.init)))
      (.seq (program rep data samplingCode cost primitive source.store source.body)
        (.atomic (QP.fst _ _)))

theorem closed_denote (sampling : Machine.SamplingCosts) {Γ a} (source : Machine.Code Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    (closed rep data samplingCode cost primitive source).denote env =
      Run.value <$> source.run cost sampling env := by
  simp only [closed, Code.denote, pure_bind, bind_pure_comp]
  rw [program_denote rep data samplingCode cost primitive sampling]
  simp [Machine.Code.run, Expr.run_value, bind_pure_comp, Functor.map_map]

theorem compiled_closed_erase {control : ControlCosts}
    {queryCost : (i : Nat) → unifSpec.Range i → Nat}
    (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
    (sampling : Machine.SamplingCosts) {Γ a} (source : Machine.Code Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    Run.value <$> backend.execute
      (backend.compile (closed rep data samplingCode cost primitive source)) env =
        Run.value <$> source.run cost sampling env := by
  rw [backend.compile_erase, closed_denote rep data samplingCode cost primitive sampling]

end Signatures.Runtime.BackendProgram.MachineCompiler
