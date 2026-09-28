import Signatures.Runtime.Arithmetic
import Signatures.Runtime.Inlining
import Signatures.Runtime.Data
import VCVio.OracleComp.Constructions.SampleableType

/-! A general closed target language. The only effects are primitive randomness and
read/write of a typed store; hash or signature simulation is not a target instruction.
Compound immutable values are references, as in the stack/list expression interpreter.
Store reads/writes are register operations, not deep copies. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Machine

inductive Effect (store : Ty CryptoAtom) : Ty CryptoAtom → Ty CryptoAtom → Type
  | scalar : Effect store .unit scalar
  | uniform (n : Nat) : Effect store .unit (boundedNat n)
  | read : Effect store .unit store
  | write : Effect store store .unit

structure SamplingCosts where
  scalar : Nat
  uniform : Nat → Nat

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq K] [DecidableEq M]

noncomputable def effects (sampling : SamplingCosts) (store : Ty CryptoAtom) :
    HandlerM (cryptoBase F G₁ G₂ K M) (Effect store)
      (StateT (store.Value (cryptoBase F G₁ G₂ K M)) ProbComp) := fun cmd arg state => match cmd with
  | .scalar => (fun x => (⟨x, sampling.scalar⟩, state)) <$> ($ᵗ F : ProbComp F)
  | .uniform n => (fun x => (⟨x, sampling.uniform n⟩, state)) <$>
      (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .read => pure (⟨state, 1⟩, state)
  | .write => pure (⟨(), 1⟩, arg)

/-- Initial storage must be built by an expression over the actual input registers.
There is no host-language initializer or arbitrary semantic oracle handler. -/
structure Code (inputs : List (Ty CryptoAtom)) (output : Ty CryptoAtom) where
  store : Ty CryptoAtom
  init : Expr CryptoOp inputs store
  body : Program CryptoOp (Effect store) inputs output

noncomputable def Code.run {inputs output} (code : Code inputs output)
    (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (env : Env (cryptoBase F G₁ G₂ K M) inputs) : ProbComp (Run (output.Value (cryptoBase F G₁ G₂ K M))) := do
  let initial := code.init.run (arithmetic F G₁ G₂ K M cost) env
  let p ← (code.body.run (arithmetic F G₁ G₂ K M cost) (effects sampling code.store) env).run initial.value
  pure ⟨p.1.value, initial.steps + p.1.steps + 2⟩

/-- Fixed first-order data is independent of the input challenge. Its complete structural
load and the input-register spine are charged before executing the code. -/
structure Package (base : CryptoAtom → Type) (inputs : List (Ty CryptoAtom)) (output : Ty CryptoAtom) where
  dataTypes : List (Ty CryptoAtom)
  data : Env base dataTypes
  code : Code (inputs ++ dataTypes) output

noncomputable def Package.run {inputs output}
    (pack : Package (cryptoBase F G₁ G₂ K M) inputs output)
    (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (env : Env (cryptoBase F G₁ G₂ K M) inputs) :
    ProbComp (Run (output.Value (cryptoBase F G₁ G₂ K M))) := do
  let data := Env.load pack.data
  let frame := Env.attach env data.value
  let r ← pack.code.run cost sampling frame.value
  pure ⟨r.value, data.steps + frame.steps + r.steps + 1⟩

theorem Package.run_eq {inputs output}
    (pack : Package (cryptoBase F G₁ G₂ K M) inputs output)
    (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (env : Env (cryptoBase F G₁ G₂ K M) inputs) :
    pack.run cost sampling env =
      (fun r => ⟨r.value, r.steps + (Env.load pack.data).steps + inputs.length + 2⟩) <$>
        pack.code.run cost sampling (Env.append env pack.data) := by
  simp only [run, Env.load_value, Env.attach_value, Env.attach_steps, bind_pure_comp]
  congr 1
  funext r
  congr 1
  omega

/-- Resource class for arbitrary code in the closed language, not a reduction-specific
class. A certificate includes both exact behavior and a bound on every input/response path.
Input-register values are externally supplied; fixed data is loaded and fully charged. -/
def Within (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (inputs : List (Ty CryptoAtom)) (output : Ty CryptoAtom) (budget : Nat)
    (algorithm : Env (cryptoBase F G₁ G₂ K M) inputs → ProbComp (output.Value (cryptoBase F G₁ G₂ K M))) : Prop :=
  ∃ code : Package (cryptoBase F G₁ G₂ K M) inputs output,
    (∀ env, Run.value <$> code.run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost sampling env = algorithm env) ∧
    ∀ env r, r ∈ support (code.run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost sampling env) → r.steps ≤ budget

theorem Within.mono (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (inputs : List (Ty CryptoAtom)) (output : Ty CryptoAtom) {budget budget' : Nat}
    (algorithm : Env (cryptoBase F G₁ G₂ K M) inputs → ProbComp (output.Value (cryptoBase F G₁ G₂ K M)))
    (h : Within cost sampling inputs output budget algorithm) (hle : budget ≤ budget') :
    Within cost sampling inputs output budget' algorithm := by
  obtain ⟨code, he, hb⟩ := h
  exact ⟨code, he, fun env r hr => (hb env r hr).trans hle⟩

theorem Code.steps_pos {inputs output} (code : Code inputs output)
    (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (env : Env (cryptoBase F G₁ G₂ K M) inputs)
    (r : Run (output.Value (cryptoBase F G₁ G₂ K M)))
    (hr : r ∈ support (code.run cost sampling env)) : 2 < r.steps := by
  simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨p, _, rfl⟩ := hr
  have h := code.init.steps_pos (arithmetic F G₁ G₂ K M cost) env
  dsimp
  omega

theorem Package.steps_pos {inputs output}
    (pack : Package (cryptoBase F G₁ G₂ K M) inputs output)
    (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (env : Env (cryptoBase F G₁ G₂ K M) inputs)
    (r : Run (output.Value (cryptoBase F G₁ G₂ K M)))
    (hr : r ∈ support (pack.run cost sampling env)) : 2 < r.steps := by
  rw [run_eq] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  have hb := pack.code.steps_pos cost sampling (Env.append env pack.data) z hz
  dsimp
  omega

/-- A nonempty input type cannot certify any algorithm at zero cost. The witness program
must execute its initialization even if it makes no queries and returns a constant. -/
theorem Within.two_lt (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (inputs : List (Ty CryptoAtom)) (output : Ty CryptoAtom) {budget : Nat}
    (algorithm : Env (cryptoBase F G₁ G₂ K M) inputs → ProbComp (output.Value (cryptoBase F G₁ G₂ K M)))
    (h : Within cost sampling inputs output budget algorithm)
    (env : Env (cryptoBase F G₁ G₂ K M) inputs) : 2 < budget := by
  obtain ⟨code, _, hb⟩ := h
  obtain ⟨r, hr⟩ := support_nonempty
    (code.run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost sampling env)
  exact (code.steps_pos cost sampling env r hr).trans_le (hb env r hr)

end Signatures.Runtime.Machine
