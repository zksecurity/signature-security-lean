import Proofs.Runtime.Machine
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime OracleComp OracleSpec

namespace SignaturesTest.RuntimeMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨7, fun n => n + 1⟩
private def primitives := arithmetic F F F Bool Bool cost

private def echoStore : Machine.Code [.nat] .nat where
  store := .nat
  init := .nat 0
  body := .bind (.query .write (.var .here)) (.query .read .unit)

example (n : Nat) : echoStore.run (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Bool)
    cost sampling (n, ()) = pure ⟨n, 10⟩ := by
  dsimp [Machine.Code.run, echoStore, Program.run, Expr.run, Var.get, Var.depth,
    Machine.effects, StateT.run, StateT.bind, StateT.pure]
  simp

private def initialized : Machine.Code [] .nat where
  store := .nat
  init := .nat 41
  body := .query .read .unit

example : initialized.run (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Bool)
    cost sampling () = pure ⟨41, 47⟩ := by
  dsimp [Machine.Code.run, initialized, Program.run, Expr.run, Machine.effects,
    StateT.run, StateT.bind, StateT.pure]
  simp

private def inspectKey : Machine.Code [point₂] .nat where
  store := .unit
  init := .unit
  body := .branch (.op .point₂Eq (.pair (.var .here) (.op .zero₂ .unit)))
    (.ret (.nat 7)) (.ret (.nat 11))

-- The implementation class must allow the adversary to observe and branch on its key.
example (pk : F) : inspectKey.run (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Bool)
    cost sampling (pk, ()) = if pk = 0 then pure ⟨7, 20⟩ else pure ⟨11, 24⟩ := by
  by_cases hpk : pk = 0 <;>
    dsimp [Machine.Code.run, inspectKey, Program.run, Expr.run, Var.get, Var.depth,
      arithmetic, CryptoOp.price, cost, PrimitiveCosts.unit, StateT.run, StateT.bind, StateT.pure] <;>
    simp [hpk] <;> change _ <$> pure (_, ()) = _ <;> simp

private inductive Capability : Ty CryptoAtom → Ty CryptoAtom → Type
  | double : Capability .nat .nat

private def routines {a b} : Capability a b → Program CryptoOp (Machine.Effect .unit) [a] b
  | .double => .ret (.op .natAdd (.pair (.var .here) (.var .here)))

private def callDouble : Program CryptoOp Capability [] .nat := .query .double (.nat 3)

private def inlined : Machine.Code [] .nat := ⟨.unit, .unit, callDouble.inline routines⟩

-- Three additional call-frame steps are real work, not an opaque capability price.
example : inlined.run (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Bool)
    cost sampling () = pure ⟨6, 17⟩ := by
  dsimp [Machine.Code.run, inlined, callDouble, Program.inline, routines, Program.run,
    Args.run, Expr.run, Var.get, Var.depth, cost, arithmetic, CryptoOp.price,
    PrimitiveCosts.unit, StateT.run, StateT.bind, StateT.pure]
  simp

example : (callDouble.inline routines).run primitives (Machine.effects sampling .unit) () =
    callDouble.run primitives (routineHandler primitives (Machine.effects sampling .unit) routines) () :=
  callDouble.inline_run primitives (Machine.effects sampling .unit) routines ()

example (algorithm : Env (cryptoBase F F F Bool Bool) [] → ProbComp Nat) :
    ¬ Machine.Within cost sampling [] .nat 0 algorithm := by
  intro h
  have hp := h.two_lt cost sampling [] .nat algorithm ()
  omega

end SignaturesTest.RuntimeMachine

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Args.run_value, ``Args.steps_pos, ``Program.inline_run,
      ``Program.inline_denote, ``Machine.Code.steps_pos, ``Machine.Within.mono,
      ``Machine.Within.two_lt] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
