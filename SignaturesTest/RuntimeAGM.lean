import Proofs.Runtime.AGMTable
import Proofs.Runtime.TableRefinement
import Proofs.Runtime.KeyEquality
import Proofs.Runtime.AffineTable
import Proofs.Runtime.Weights
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime OracleComp OracleSpec

namespace SignaturesTest.RuntimeAGM

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨7, fun _ => 1⟩
private def primitives := arithmetic F F F Bool Unit cost
private def scalarIndex := index (cell := scalar) CryptoOp.natEq CryptoOp.natSub

-- Empty and out-of-range indexing return the default; a stored zero is still a hit.
example (n : Nat) : scalarIndex.run primitives (n, 1, [], ()) = ⟨1, 13⟩ := rfl
example : scalarIndex.run primitives (0, 1, [0, 2, 4], ()) = ⟨0, 54⟩ := rfl
example : scalarIndex.run primitives (2, 1, [0, 2, 4], ()) = ⟨4, 90⟩ := rfl
example : scalarIndex.run primitives (3, 1, [0, 2, 4], ()) = ⟨1, 97⟩ := rfl

example (n : Nat) (xs : List F) :
    (scalarIndex.run primitives (n, 0, xs, ())).steps ≤ xs.length * 28 + 13 := by
  exact index_steps_le (cell := scalar) primitives CryptoOp.natEq CryptoOp.natSub 1
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) n 0 xs

-- A full table has one sample per domain element, even without any source queries.
example (z : Run (List F) × Nat)
    (hz : z ∈ support (((sampleTable (Machine.Effect.scalar (store := .nat))).run
      primitives (Machine.effects sampling .nat) (3, ())).run 42)) :
    z.2 = 42 ∧ z.1.value.length = 3 ∧ z.1.steps ≤ 82 :=
  AGM.sampleTable_bound cost sampling .nat 3 42 z hz

example : (fun z => tableFunction (ι := Bool) (0 : F) z.1.value) <$>
    ((sampleTable (Machine.Effect.scalar (store := .nat))).run primitives
      (Machine.effects sampling .nat) (Fintype.card Bool, ())).run 42 =
    @uniformSample (Bool → F) (instSampleableTypePiFintype) :=
  AGM.sampleTable_function Bool cost sampling .nat 42

-- Zero-length domains still pay the executed loop/reversal overhead.
example : ((sampleTable (Machine.Effect.scalar (store := .nat))).run primitives
    (Machine.effects sampling .nat) (0, ())).run 42 = pure (⟨[], 10⟩, 42) := by
  dsimp [sampleTable, sampleList, Program.run, repeatRun, Expr.run, reverseList, foldRun,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure]
  simp [foldRun]

example : Weights.bls.run primitives (false, false, ()) = ⟨1, 10⟩ := rfl
example : Weights.bls.run primitives (false, true, ()) = ⟨0, 10⟩ := rfl

example : ((Weights.oops 3).run primitives ((false, 2), (2, false), ())).value = (4 : F) := by
  have hv := Weights.oops_value (G₁ := F) (G₂ := F) (M := Unit) cost 3
    (false, 2) ((2 : F), false)
  norm_num [OOPS.Handle.oopsWMulti] at hv
  exact hv

example : ((Weights.oops 3).run primitives ((false, 2), (2, false), ())).steps = 65 := by
  rfl

example : (Weights.oops 3).run primitives ((false, 2), (2, true), ()) = ⟨0, 12⟩ := rfl
example : (Weights.oops 0).run primitives ((false, 0), (2, false), ()) = ⟨1, 22⟩ := rfl

example : ((Weights.oops 3).run primitives ((false, 3), (2, false), ())).steps ≤ 76 :=
  Weights.oops_steps_le cost 3 (false, 3) ((2 : F), false)

-- Proximity's zero tag is the constant coordinate; other tags use charged indexing.
example : ((Weights.proximity 3).run primitives ((0, false), ([2, 3, 4], false), ())).value = (1 : F) := by
  exact Weights.proximity_value cost 3 (0, false) ([2, 3, 4], false)

example : ((Weights.proximity 3).run primitives ((3, false), ([2, 3, 4], false), ())).value = (4 : F) := by
  exact Weights.proximity_value cost 3 (3, false) ([2, 3, 4], false)

example : ((Weights.proximity 3).run primitives ((3, false), ([2], false), ())).value = (0 : F) := by
  exact Weights.proximity_value cost 3 (3, false) ([2], false)

example : ((Weights.proximity 3).run primitives ((3, false), ([2, 3, 4], true), ())).value = (0 : F) := by
  exact Weights.proximity_value cost 3 (3, false) ([2, 3, 4], true)

example (xs : List F) : ((Weights.proximity 3).run primitives ((3, false), (xs, false), ())).steps ≤
    xs.length * 28 + 51 :=
  Weights.proximity_steps_le cost 3 (3, false) (xs, false)

example (m : Fin 3 → F) (k : Fin 3) :
    ((Weights.proximity 3).run primitives
      (Weights.encodeProximityKey (some k, false), (List.ofFn m, false), ())).value = m k := by
  have hv := Weights.proximity_native (G₁ := F) (G₂ := F) (M := Unit) cost 3
    (some k, false) (List.ofFn m, false)
  rw [Weights.decodeProximityMessage_ofFn] at hv
  simpa only [primitives, Proximity.Proofs.coordinateWeight, eq_self, ite_true] using hv

-- Construction preserves enumeration order and does not discard repeated keys or zeroes.
example : (AGM.attachTable (indexTy := key)).run primitives (1, [], [], ()) = ⟨[], 15⟩ := rfl

example : ((AGM.attachTable (indexTy := key)).run primitives
    (1, [false, true, false], [0, 2], ())).value = [(false, 0), (true, 2), (false, 1)] := rfl

example : ((AGM.attachTable (indexTy := key)).run primitives
    (1, [false, true, false], [0, 2], ())).steps ≤ 375 :=
  AGM.attachTable_steps_le (indexTy := key) cost 1 [false, true, false] [0, 2]

example : (AGM.weightedSum Weights.bls).run primitives (false, [], ()) = ⟨0, 7⟩ := rfl
example : (AGM.weightedSum Weights.bls).run primitives
    (false, [(false, 2), (true, 3)], ()) = ⟨2, 85⟩ := rfl

example (xs : List (Bool × F)) (m : Bool) :
    ((AGM.weightedSum Weights.bls).run primitives (m, xs, ())).steps ≤ xs.length * 39 + 7 := by
  exact AGM.weightedSum_steps_le cost Weights.bls m xs 10
    (fun i => le_of_eq (Weights.bls_steps cost i m))

example (values : List F) (m : Bool) :
    ((AGM.weightedSum Weights.bls).run primitives
      (m, (AGM.attachTable.run primitives (0, AGM.canonicalKeys (id : Bool → Bool), values, ())).value,
        ())).value = ∑ i : Bool, tableFunction 0 values i * BLS.Proofs.indicatorWeight i m := by
  have h := AGM.weightedSum_native (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
    (indexTy := key) cost (id : Bool → Bool) 0 values Weights.bls m
  simpa only [primitives, Weights.bls_value (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit),
    id_eq] using h

example : (AGM.KeyEquality.oops 3).run primitives ((false, 2), (false, 2), ()) = ⟨true, 21⟩ := rfl
example : (AGM.KeyEquality.oops 3).run primitives ((false, 2), (false, 1), ()) = ⟨false, 21⟩ := rfl
example : (AGM.KeyEquality.oops 3).run primitives ((false, 2), (true, 2), ()) = ⟨false, 10⟩ := rfl
example : (AGM.KeyEquality.proximity 3).run primitives ((2, false), (2, false), ()) = ⟨true, 21⟩ := rfl
example : (AGM.KeyEquality.proximity 3).run primitives ((2, false), (1, false), ()) = ⟨false, 21⟩ := rfl
example : (AGM.KeyEquality.proximity 3).run primitives ((2, false), (2, true), ()) = ⟨false, 10⟩ := rfl

example : (lookupExpr (val := scalar) AGM.KeyEquality.bls).run primitives
    (false, 1, [(false, 0), (true, 2), (false, 4)], ()) = ⟨(true, 0), 55⟩ := rfl

example (xs : List ((Bool × Fin 4) × F)) (i : Bool × Fin 4) :
    ((lookupExpr (val := scalar) (AGM.KeyEquality.oops 3)).run primitives (i, 0, xs, ())).steps ≤
      xs.length * 43 + 9 :=
  lookupExpr_steps_le (val := scalar) primitives (AGM.KeyEquality.oops 3) 21
    (fun x y => AGM.KeyEquality.oops_steps_le cost 3 x y) i 0 xs

example (values : List F) (i : Bool) :
    ((lookupExpr (val := scalar) AGM.KeyEquality.bls).run primitives
      (i, 0, (AGM.attachTable.run primitives (0, AGM.canonicalKeys (id : Bool → Bool), values, ())).value,
        ())).value = (true, tableFunction 0 values i) := by
  exact AGM.lookupExpr_native (indexTy := key) cost (id : Bool → Bool) Function.injective_id
    0 values AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y) i

example : (AGM.affineRows (indexTy := key)).run primitives (1, 2, [], ()) = ⟨[], 11⟩ := rfl

example : (AGM.affineRows (indexTy := key)).run primitives
    (1, 2, [((false, 2), 3), ((true, 4), 1)], ()) = ⟨[(false, 2), (true, 4)], 87⟩ := rfl

example (xs : List ((Bool × F) × F)) (g X : F) :
    ((AGM.affineRows (indexTy := key)).run primitives (g, X, xs, ())).steps ≤ xs.length * 38 + 11 :=
  AGM.affineRows_steps_le (indexTy := key) cost g X xs

-- Pairing the independent scalar samples precedes the charged affine-base calculation.
example : ((AGM.affineRows (indexTy := key)).run primitives
    (1, 2, ((AGM.attachTable (indexTy := .pair key scalar)).run primitives
      (0, [(false, 2), (true, 4)], [3, 1], ())).value, ())).value = [(false, 2), (true, 4)] := rfl

end SignaturesTest.RuntimeAGM

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``indexStep_value, ``index_denote, ``index_steps_le,
      ``Var.weakenTail_get, ``Var.weakenTail_depth, ``Expr.weakenTail_run, ``Expr.weakenTail_denote,
      ``sampleTable_length, ``uniform_function_vector, ``sampleTable_function,
      ``repeatRun_run_state, ``drawAndCons_run_state, ``sampleList_run_state, ``sampleTable_run_state,
      ``AGM.sampleTable_run, ``AGM.sampleTable_bound, ``AGM.sampleTable_uniform, ``AGM.sampleTable_function,
      ``Weights.bls_value, ``Weights.bls_steps, ``Weights.power_value, ``Weights.power_steps_le,
      ``Weights.oops_value, ``Weights.oops_steps_le, ``Weights.proximity_value,
      ``Weights.proximity_steps_le, ``Weights.proximity_native, ``Weights.decodeProximityMessage_ofFn,
      ``AGM.weightedSumBody_run, ``AGM.weightedSum_value, ``AGM.weightedSum_steps_le,
      ``AGM.attachStep_fold, ``AGM.attachBody_run, ``AGM.attachBody_value,
      ``AGM.attachFold_value, ``AGM.attachTable_value, ``AGM.attachBody_steps_le,
      ``AGM.attachFold_steps_le, ``AGM.attachTable_steps_le,
      ``AGM.canonicalKeys_length, ``AGM.canonicalKeys_attach, ``AGM.canonicalKeys_sum,
      ``AGM.attachTable_native, ``AGM.weightedSum_native,
      ``lookup_fold, ``lookupExprBody_value, ``lookupExpr_value, ``lookupExprBody_steps_le,
      ``lookupExpr_steps_le, ``AGM.KeyEquality.bls_value, ``AGM.KeyEquality.bls_steps,
      ``AGM.KeyEquality.oops_value, ``AGM.KeyEquality.oops_steps_le,
      ``AGM.KeyEquality.proximity_value, ``AGM.KeyEquality.proximity_steps_le,
      ``Weights.encodeProximityKey_injective, ``AGM.lookupValue_map, ``AGM.lookupValue_canonical,
      ``AGM.lookupExpr_native, ``AGM.affineBody_run, ``AGM.affineFold_value, ``AGM.affineRows_value,
      ``AGM.affineFold_steps_le, ``AGM.affineRows_steps_le, ``AGM.affineRows_native] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
