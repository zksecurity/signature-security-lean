import Signatures.Runtime.HeapProgramCost
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime HeapBits SharedHeap WeierstrassCurve OracleComp

namespace SignaturesTest.ProgramTrace

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def curve : Affine (ZMod 3) := ⟨0, 0, 0, 1, 1⟩
private def H : AddSubgroup curve.Point := ⊥
private instance : Module (ZMod 3) H := EllipticCurveCircuit.subgroupModule curve H (by
  intro P
  have hp : P = 0 := Subtype.ext (by simpa [H] using P.property)
  simp [hp])

private abbrev base := cryptoBase (ZMod 3) H H (BitVec 16) (BitVec 16)
private abbrev spec : OracleSpec Unit := fun _ => Bool
private abbrev NoCmd (_ _ : Ty CryptoAtom) : Type := Empty
private def primitives := arithmetic (ZMod 3) H H (BitVec 16) (BitVec 16) PrimitiveCosts.unit
private def reference : HandlerM base NoCmd (StateT Unit (OracleComp spec)) :=
  fun cmd _ => nomatch cmd
private def implementation : HeapProgram.HandlerM NoCmd (StateT Unit (OracleComp spec)) :=
  fun cmd _ _ => nomatch cmd

private def code : Program CryptoOp NoCmd [] .nat :=
  .loop (.nat 2) (.nat 0) (.ret (.var .here))

private theorem source_budget : ∀ out ∈ support ((code.run primitives reference ()).run ()),
    0+out.1.steps ≤ 16 := by
  intro out hout
  simp only [code, Program.run, Expr.run, repeatRun, StateT.run_pure,
    pure_bind, Var.get, Var.depth, support_pure, Set.mem_singleton_iff] at hout
  subst out
  decide

-- The caller supplies only the total source budget, not loop-body width checks.
example : NaturalRange.ProgramTrace PrimitiveCosts.unit 16 reference code () () :=
  NaturalRange.program_trace_bound PrimitiveCosts.unit reference (fun _ (_ : Unit) => True)
    (by intros; trivial) (by intro a b cmd; cases cmd) code 0 16 () trivial () trivial source_budget

-- A concrete application of the whole-program theorem, including counted loops.
example : QueryTreeRel
    (fun actual source => HeapProgram.Post 16 49
      (atomRep (r := 3) H H (id : BitVec 16 → BitVec 16) id) (fun _ (_ _ : Unit) => True)
      [] source.1.steps actual source)
    (((HeapProgram.compile 16 3 curve curve code).run implementation [] empty).run ())
    ((code.run primitives reference ()).run ()) := by
  exact HeapProgram.compile_refines_of_budget H H id id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit reference implementation
    (fun _ (_ _ : Unit) => True) (by intros; trivial) (by intro a b cmd; cases cmd)
    (fun _ (_ : Unit) => True) (by intros; trivial) (by intro a b cmd; cases cmd)
    code [] [] () empty () () empty_represents trivial .nil trivial 0 trivial trivial source_budget

private def deadBranch : Program CryptoOp NoCmd [] .nat :=
  .branch (.bool false) (.ret (.nat 1000)) (.ret (.nat 0))

-- The same source budget now certifies actual controller steps as well as
-- semantics and allocations. The multiplier is computed from program syntax.
example : QueryTreeRel
    (fun actual source => HeapProgram.CostPost 16 49
      (atomRep (r := 3) H H (id : BitVec 16 → BitVec 16) id) (fun _ (_ _ : Unit) => True)
      [] (HeapProgram.budget 16 16 (fun cmd => nomatch cmd) code) actual source ∧
      actual.1.steps ≤ 16*HeapProgram.budget 16 16 (fun cmd => nomatch cmd) code)
    (((HeapProgram.compile 16 3 curve curve code).run implementation [] empty).run ())
    ((code.run primitives reference ()).run ()) := by
  exact HeapProgram.compile_costed_of_budget H H id id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit (fun cmd => nomatch cmd)
    reference implementation (fun _ (_ _ : Unit) => True) (by intros; trivial)
    (fun _ (_ : Unit) => True) (by intros; trivial) (by intro a b cmd; cases cmd)
    code [] [] () empty () () empty_represents trivial .nil trivial
    0 16 trivial trivial (by decide) (by intro out hout; have h := source_budget out hout; omega)
    (by intro a b cmd; cases cmd)

-- Untaken branches are not incorrectly required to fit the selected word width.
example : NaturalRange.ProgramTrace PrimitiveCosts.unit 4 reference deadBranch () () := by
  apply NaturalRange.program_trace_bound PrimitiveCosts.unit reference (fun _ (_ : Unit) => True)
    (by intros; trivial) (by intro a b cmd; cases cmd) deadBranch 0 4 () trivial () trivial
  intro out hout
  simp only [deadBranch, Program.run, Expr.run, Bool.false_eq_true, ite_false,
    StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
  subst out
  decide

private inductive Cmd : Ty CryptoAtom → Ty CryptoAtom → Type
  | oversized : Cmd .unit .nat

private def oversized : HandlerM base Cmd (StateT Unit (OracleComp spec))
  | _, _, .oversized, _ => pure ⟨1000, 0⟩

-- Cheap source prices alone cannot justify encoding an oversized oracle reply.
example : ¬ NaturalRange.ProgramTrace PrimitiveCosts.unit 4 oversized
    (Program.query .oversized (.unit : Expr CryptoOp [] .unit)) () () := by
  intro h
  have hr := h.2 (⟨1000, 0⟩, ()) (by simp [oversized])
  change 1000 < 2^4 at hr
  norm_num at hr

private inductive Coin : Ty CryptoAtom → Ty CryptoAtom → Type
  | toss : Coin .unit .bool

open scoped OracleSpec.PrimitiveQuery in
private def coinReference : HandlerM base Coin (StateT Unit (OracleComp spec))
  | _, _, .toss, _ => fun state => do
    let b ← (liftM (spec.query ()) : OracleComp spec Bool)
    pure (⟨b, 1⟩, state)

open scoped OracleSpec.PrimitiveQuery in
private def coinImplementation : HeapProgram.HandlerM Coin (StateT Unit (OracleComp spec))
  | _, _, .toss, _, store => fun state => do
    let b ← (liftM (spec.query ()) : OracleComp spec Bool)
    let out := alloc store (.word [b])
    pure (⟨some out.value, out.steps+1⟩, state)

private def adaptive : Program CryptoOp Coin [] .nat :=
  .bind (.query .toss .unit) (.branch (.var .here) (.ret (.nat 1)) (.ret (.nat 0)))

private theorem coin_trace : NaturalRange.ProgramTrace PrimitiveCosts.unit 16 coinReference adaptive () () := by
  constructor
  · exact ⟨trivial, fun _ _ => trivial⟩
  · intro out _
    refine ⟨trivial, ?_⟩
    change if out.1.value then 1 < 2^16 else 0 < 2^16
    split <;> norm_num

-- The compiler proof also instantiates with a real oracle query and a branch
-- chosen from its reply. No semantic decoder is used by the bit handler.
example : QueryTreeRel
    (fun actual source => HeapProgram.Post 16 49
      (atomRep (r := 3) H H (id : BitVec 16 → BitVec 16) id) (fun _ (_ _ : Unit) => True)
      [] source.1.steps actual source)
    (((HeapProgram.compile 16 3 curve curve adaptive).run coinImplementation [] empty).run ())
    ((adaptive.run primitives coinReference ()).run ()) := by
  apply HeapProgram.compile_refines H H id id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit coinReference coinImplementation
    (fun _ (_ _ : Unit) => True) (by intros; trivial) ?_
    adaptive [] [] () empty () () empty_represents trivial .nil trivial coin_trace
  intro a b cmd heap root store impl x state hs hw _ _ _
  cases cmd with
  | toss =>
    apply QueryTreeRel.queryBind ()
    intro b
    apply QueryTreeRel.pure
    refine ⟨[.word [b]], _, _, rfl, alloc_represents store heap hs _, ?_, ?_, trivial, by simp⟩
    · apply wellFormed_append heap _ hw
      change 1 ≤ 49
      decide
    · exact .bool (alloc_lookup store heap hs _)

private def coinFee : {a b : Ty CryptoAtom} → Coin a b → Nat :=
  fun _ => HeapExpression.allocBudget 49 20 + 1

-- This handler's bit cost is proved from its concrete heap allocation, not
-- assumed to equal the source oracle price. Both possible replies are covered.
example : QueryTreeRel
    (HeapProgram.CostPost 16 49
      (atomRep (r := 3) H H (id : BitVec 16 → BitVec 16) id) (fun _ (_ _ : Unit) => True)
      [] (HeapProgram.budget 16 20 coinFee adaptive))
    (((HeapProgram.compile 16 3 curve curve adaptive).run coinImplementation [] empty).run ())
    ((adaptive.run primitives coinReference ()).run ()) := by
  apply HeapProgram.compile_costed H H id id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit
    20 (HeapProgram.budget 16 20 coinFee adaptive) coinFee coinReference coinImplementation
    (fun _ (_ _ : Unit) => True) (by intros; trivial) ?_
    adaptive [] [] () empty () () empty_represents trivial .nil trivial coin_trace ?_ (le_refl _)
  · intro a b cmd heap root store impl x state hs hw _ _ _ hn
    cases cmd with
    | toss =>
      apply QueryTreeRel.queryBind ()
      intro b
      apply QueryTreeRel.pure
      constructor
      · refine ⟨[.word [b]], _, _, rfl, alloc_represents store heap hs _, ?_, ?_, trivial, by simp⟩
        · apply wellFormed_append heap _ hw
          change 1 ≤ 49
          decide
        · exact .bool (alloc_lookup store heap hs _)
      · have halloc := HeapExpression.alloc_le_budget hw hn store hs (.word [b]) (by
          change 1 ≤ 49
          decide)
        change (alloc store (.word [b])).steps+1 ≤ 1*_ + (HeapExpression.allocBudget 49 20+1)
        change _ ≤ HeapExpression.allocBudget 49 20 at halloc
        omega
  · intro out hout
    simp only [adaptive, Program.run, Expr.run, Var.get, Var.depth, coinReference,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨r, hr, hout⟩ := hout
    simp only [StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨b, _, rfl⟩ := hr
    cases b <;> simp at hout <;> subst out <;> decide

end SignaturesTest.ProgramTrace

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``NaturalRange.program_trace_bound, ``QueryTreeRel.with_support,
      ``QueryTreeRel.bind_support, ``HeapProgram.Post.mono, ``HeapProgram.Post.rebase,
      ``HeapProgram.Post.state_mono, ``HeapProgram.loop_refines,
      ``HeapProgram.compile_refines, ``HeapProgram.compile_refines_of_budget,
      ``HeapProgram.loop_costed, ``HeapProgram.compile_costed,
      ``HeapProgram.compile_costed_of_budget] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
