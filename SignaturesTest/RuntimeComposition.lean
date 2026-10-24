import Proofs.Runtime.Arithmetic
import Proofs.Runtime.Cache
import Proofs.Runtime.Coron
import Proofs.Runtime.GrowingState
import Proofs.Runtime.Sampling
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime OracleComp OracleSpec

namespace SignaturesTest.RuntimeComposition

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private abbrev Base := cryptoBase F F F Bool Bool
private def primitives := arithmetic F F F Bool Bool PrimitiveCosts.unit

private inductive Draw : Ty CryptoAtom → Ty CryptoAtom → Type
  | scalar : Draw .unit scalar

private def replies : ReplyContract Base Draw where
  allows _ _ _ := True
  responds cmd _ := by cases cmd; exact ⟨0, trivial⟩

private theorem initializer_budget (n : Nat) :
    SourceBudget primitives replies (fun _ => ()) (sampleTable (Op := CryptoOp) Draw.scalar)
      (n, ()) (17 * n + 10) (fun _ : Unit => n) := by
  intro price z hz
  have hdraw : ∀ r ∈ support (pricedRequests replies (fun _ => price ()) Draw.scalar ()),
      r.steps ≤ price () := by
    intro r hr
    simp only [pricedRequests, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    exact le_rfl
  have h := sampleTable_steps_le primitives (pricedRequests replies (fun _ => price ()))
    Draw.scalar (price ()) hdraw n z hz
  simpa [Nat.mul_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

-- A test handler with increasing cost checks the amortized theorem, not a crypto implementation.
private def growingDraw : HandlerM Base Draw (StateT Nat ProbComp) := fun cmd _ => match cmd with
  | .scalar => fun count => pure (⟨2, 7 + 3 * count⟩, count + 1)

example (n : Nat) (z : Run (List F) × Nat)
    (hz : z ∈ support (((sampleTable (Op := CryptoOp) Draw.scalar).run primitives growingDraw (n, ())).run 0)) :
    z.1.steps ≤ 24 * n + 10 + 3 * n ^ 2 := by
  have h := SourceBudget.growing_handler_bound primitives replies (fun _ => ())
    (sampleTable (Op := CryptoOp) Draw.scalar) (n, ()) (17 * n + 10) (fun _ : Unit => n)
    (initializer_budget n) growingDraw (fun _ => 7) 3 (fun _ => True) id
    (by
      intro a b cmd arg state hi p hp
      cases cmd
      simp only [growingDraw, StateT.run, support_pure, Set.mem_singleton_iff] at hp
      subst p
      simp [replies]) 0 trivial rfl z hz
  have hb := h.2
  simp only [Fintype.sum_unique] at hb
  nlinarith

-- Growth does not silently assume an empty initial state.
example (n : Nat) (z : Run (List F) × Nat)
    (hz : z ∈ support (((sampleTable (Op := CryptoOp) Draw.scalar).run primitives growingDraw (n, ())).run 13)) :
    z.2 ≤ 13 + n := by
  have h := SourceBudget.state_growth primitives replies (fun _ => ())
    (sampleTable (Op := CryptoOp) Draw.scalar) (n, ()) (17 * n + 10) (fun _ : Unit => n)
    (initializer_budget n) growingDraw (fun _ => 1) (fun _ => True) id
    (by
      intro a b cmd arg state hi p hp
      cases cmd
      simp only [growingDraw, StateT.run, support_pure, Set.mem_singleton_iff] at hp
      subst p
      simp [replies]) 13 trivial z hz
  simpa using h.2

private def fixedDraw (value : F) : Handler Base Draw unifSpec := fun cmd _ => match cmd with
  | .scalar => pure ⟨value, 7⟩

example : (cacheHandler primitives (fixedDraw 2) CryptoOp.keyEq Draw.scalar 0 true).run [] =
    pure (⟨2, 43⟩, [(true, 2)]) := by
  simp [cacheHandler, cacheGet, lookup, lookupBody, Program.run, Expr.run, Var.get, Var.depth,
    foldRun, fixedDraw, StateT.run]

-- A hit returns the earlier value even if a subsequent draw would return something else.
example : (cacheHandler primitives (fixedDraw 3) CryptoOp.keyEq Draw.scalar 0 true).run [(true, 2)] =
    pure (⟨2, 47⟩, [(true, 2)]) := by
  simp [cacheHandler, cacheGet, lookup, lookupBody, Program.run, Expr.run, Var.get, Var.depth,
    foldRun, fixedDraw, StateT.run, primitives, arithmetic, CryptoOp.price, PrimitiveCosts.unit]

end SignaturesTest.RuntimeComposition

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Program.run_dominated, ``SourceBudget.potential_bound,
      ``SourceBudget.implemented_bound, ``SourceBudget.state_growth,
      ``SourceBudget.growing_handler_bound, ``cacheGet_denote, ``cacheHandler_erase,
      ``cacheHandler_steps_le, ``cacheHandler_length,
      ``Coron.hashReply_value, ``Coron.signReply_value, ``Coron.extract_value,
      ``Coron.hashReply_steps, ``Coron.signReply_steps, ``Coron.extract_steps] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
