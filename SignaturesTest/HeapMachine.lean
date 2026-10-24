import Proofs.Runtime.HeapProbability
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime HeapBits SharedHeap PrimeFieldCircuit WeierstrassCurve OracleComp
open scoped ENNReal

namespace SignaturesTest.HeapMachine

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def curve : Affine (ZMod 3) := ⟨0, 0, 0, 1, 1⟩
private def H : AddSubgroup curve.Point := ⊥
private instance : Module (ZMod 3) H := EllipticCurveCircuit.subgroupModule curve H (by
  intro P
  have hp : P = 0 := Subtype.ext (by simpa [H] using P.property)
  simp [hp])

private def prices : Machine.SamplingCosts := ⟨1, fun n => n.size+1⟩
private abbrev base := cryptoBase (ZMod 3) H H (BitVec 24) (BitVec 24)
private def primitives := arithmetic (ZMod 3) H H (BitVec 24) (BitVec 24) PrimitiveCosts.unit

private def code : Program CryptoOp (Machine.Effect (boundedNat 4)) [] (boundedNat 4) :=
  .bind (.query .scalar .unit)
    (.bind (.query (.uniform 4) .unit)
      (.bind (.query .write (.var .here)) (.query .read .unit)))

private def initial := alloc empty (.word (natBits 24 0))
private def initialHeap : List Node := [.word (natBits 24 0)]

private theorem initial_rep : Represents 24 (atomRep (r := 3) H H (id : BitVec 24 → BitVec 24) id)
    initialHeap (boundedNat 4) initial.value.1 (0 : Fin 5) := by
  apply Represents.atom (alloc_lookup empty [] empty_represents _)
  exact ⟨rfl, by change 0 < 2^24; decide⟩

private theorem source_budget : ∀ out ∈ support
    ((code.run primitives (Machine.effects prices (boundedNat 4)) ()).run 0),
    out.1.steps ≤ 18 := by
  intro out hout
  simp only [code, Program.run, Expr.run, Var.get, Var.depth,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind] at hout
  simp only [Machine.effects, StateT.run, pure_bind,
    mem_support_bind_iff, support_map, Set.mem_image, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨first, hfirst, last, hlast, rfl⟩ := hout
  obtain ⟨_, _, rfl⟩ := hfirst
  obtain ⟨_, _, rfl⟩ := hlast
  change 18 ≤ 18
  decide

-- All handler and range-growth obligations are discharged by the machine
-- compiler theorem, not by test-specific assumptions about sampler behavior.
example : QueryTreeRel
    (fun actual source => HeapProgram.CostPost 24 73
      (atomRep (r := 3) H H (id : BitVec 24 → BitVec 24) id)
      (HeapMachine.StateRel H H id id (boundedNat 4)) initialHeap
      (HeapProgram.budget 24 21 (HeapMachine.fee 24 3 2 21) code) actual source ∧
      actual.1.steps ≤ 20*HeapProgram.budget 24 21 (HeapMachine.fee 24 3 2 21) code)
    (((HeapMachine.compileBody 24 3 curve curve 2 code).run HeapMachine.Instruction.run [] initial.value.2).run
      (initial.value.1, false))
    ((code.run primitives (HeapMachine.semantics H H (w := 24) 2 prices (boundedNat 4)) ()).run (0, false)) := by
  apply HeapMachine.compileBody_costed H H id id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit 2 prices
    (fun n => (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide)
      (by change n.size ≤ n.size+1; omega)))
    code initialHeap [] () initial.value.2 (initial.value.1, false) (0, false)
    (alloc_represents empty [] empty_represents _) ?_ .nil ⟨initial_rep, rfl⟩
    0 20 trivial (by change 0 < 2^0; decide) (by decide)
    (fun out hout => (source_budget out hout).trans (by decide))
  change 24 ≤ 73 ∧ True
  decide

private def tapeOracle : QueryImpl BitRejection.bitSpec (StateM (List Bool)) :=
  fun _ tape => (tape.headD false, tape.tail)

private def closed : Machine.Code [] (boundedNat 4) :=
  ⟨boundedNat 4, .op (.finZero 4) .unit, code⟩

private theorem closed_budget : ∀ out ∈ support
    (closed.run (F := ZMod 3) (G₁ := H) (G₂ := H) (K := BitVec 24) (M := BitVec 24)
      PrimitiveCosts.unit prices ()), out.steps ≤ 24 := by
  intro out hout
  rw [Machine.Code.run] at hout
  obtain ⟨body, hbody, heq⟩ := support_bind_exists hout
  simp only [support_pure, Set.mem_singleton_iff] at heq
  subst out
  have h := source_budget body hbody
  change 3+body.1.steps+2 ≤ 24
  omega

private def samplePack : Machine.Package base [] (boundedNat 4) := ⟨[], (), closed⟩

example : MarkedProbability.bad (simulateQ HeapMachine.fairBits
    (HeapMachine.packageSemantics H H (w := 32) 7 PrimitiveCosts.unit prices samplePack ())) ≤
      27*(1/2 : ℝ≥0∞)^7 := by
  apply (HeapMachine.package_error H H 7 PrimitiveCosts.unit prices samplePack () 27
    (by decide) (by decide)
    (fun n => (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide)
      (by change n.size ≤ n.size+1; omega))) ?_).2
  intro out hout
  rw [Machine.Package.run_eq] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨source, hs, rfl⟩ := hout
  have hb := closed_budget source hs
  change source.steps+1+0+2 ≤ 27
  omega

example : QueryTreeRel
    (fun actual source => HeapExpression.ResultSpec 24 73
      (atomRep (r := 3) H H (id : BitVec 24 → BitVec 24) id) []
      source.1.steps source.1.value actual.1 ∧ actual.2 = source.2 ∧
      actual.1.steps ≤ source.1.steps*HeapMachine.budget 24 3 2 24 closed ∧
      actual.1.steps ≤ 24*HeapMachine.budget 24 3 2 24 closed)
    ((HeapMachine.compile 24 3 curve curve 2 closed).run [] empty)
    (HeapMachine.codeSemantics H H (w := 24) 2 PrimitiveCosts.unit prices closed
      (() : Env base [])) := by
  exact HeapMachine.compile_costed H H id id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit 2 prices
    (fun n => (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide)
      (by change n.size ≤ n.size+1; omega)))
    closed [] [] () empty empty_represents trivial .nil 0 24 trivial (by decide) closed_budget

private def expectedSample (n v k : Nat) (tape : List Bool) : (Nat × Bool) × List Bool :=
  let words : List (Fin (2^v)) := (List.range k).map fun i =>
    ⟨exponent ((tape.drop (v*i)).take v) % (2^v), Nat.mod_lt _ (by positivity)⟩
  let out := RejectionSampling.runTape n words
  ((out.1.map Fin.val |>.getD 0, out.1.isNone), tape.drop (v*out.2))

private def packed : Machine.Package base [boundedNat 4] (boundedNat 4) :=
  ⟨[.bool], (true, ()), ⟨boundedNat 4, .var .here,
    .branch (.var (.there .here)) (.query .read .unit) (.ret (.op (.finZero 4) .unit))⟩⟩

private theorem packed_budget (x : Fin 5) : ∀ out ∈ support
    (packed.run PrimitiveCosts.unit prices (x, ())), out.steps ≤ 20 := by
  have h : packed.run PrimitiveCosts.unit prices (x, ()) = pure ⟨x, 15⟩ := by
    simp only [Machine.Package.run_eq, packed, Machine.Code.run, Env.append, Env.load, Ty.load,
      Program.run, Expr.run, Var.get, Var.depth, pure_bind]
    simp only [StateT.run]
    rfl
  rw [h]
  intro out hout
  simp only [support_pure, Set.mem_singleton_iff] at hout
  subst out
  change 15 ≤ 20
  decide

example (x : Fin 5) : QueryTreeRel
    (fun actual source => HeapExpression.ResultSpec 24 73
      (atomRep (r := 3) H H (id : BitVec 24 → BitVec 24) id) []
      (3+source.1.steps) source.1.value actual.1 ∧ actual.2 = source.2 ∧
      actual.1.steps ≤ (3+source.1.steps+1)*HeapMachine.packageFactor 24 3 2 23 2 packed.code ∧
      actual.1.steps ≤ 24*HeapMachine.packageFactor 24 3 2 23 2 packed.code)
    ((HeapMachine.compilePackage H H id id 2 packed).run
      (HeapData.encodeEnv (r := 3) (Γ := [boundedNat 4]) H H (id : BitVec 24 → BitVec 24) id (x, ())))
    (HeapMachine.packageSemantics H H (w := 24) 2 PrimitiveCosts.unit prices packed (x, ())) := by
  apply HeapMachine.compilePackage_costed H H id id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit 2 prices
    (fun n => (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide)
      (by change n.size ≤ n.size+1; omega))) packed (x, ()) 3 20
    ⟨by change x.val < 2^3; omega, trivial⟩ ⟨trivial, trivial⟩ (by decide) (packed_budget x)

#eval show IO Unit from do
  let compiled := HeapMachine.compilePackage H H (id : BitVec 24 → BitVec 24) id 2 packed
  for i in List.range 5 do
    let input : Env base [boundedNat 4] := (Fin.ofNat 5 i, ())
    let ((out, bad), rest) :=
      (simulateQ tapeOracle (compiled.run (HeapData.encodeEnv H H id id input))).run [true, false]
    let some (root, store) := out.value | throw <| IO.userError "package failed to load its input or data"
    unless (readWord store.memory root).value == some (natBits 24 i) && !bad && rest == [true, false] do
      throw <| IO.userError "package frame order or initialized input value changed"
    unless store.count.length == 3 && out.steps ≤ 24*HeapMachine.packageFactor 24 3 2 23 2 packed.code do
      throw <| IO.userError "package allocation or complete online cost bound failed"

private def nested : Ty CryptoAtom := .pair (.list (.pair .bool .nat)) (boundedNat 4)
private def nestedValue : nested.Value base := ([(true, 2), (false, 7)], 4)

example : HeapExpression.ResultSpec 24 73
    (atomRep (r := 3) H H (id : BitVec 24 → BitVec 24) id) initialHeap
    (nested.load nestedValue).steps nestedValue
    ((HeapData.encode H H id id nested nestedValue).run [] initial.value.2) := by
  apply HeapData.encode_spec H H id id nested nestedValue initialHeap initial.value.2
    (alloc_represents empty [] empty_represents _) (by change 24 ≤ 73 ∧ True; decide)
  simp [nested, nestedValue, NaturalRange.ValueBound]

#eval show IO Unit from do
  let loader := HeapData.encode H H (id : BitVec 24 → BitVec 24) id nested nestedValue
  let out := loader.run [] initial.value.2
  let some (root, store) := out.value | throw <| IO.userError "nested data loader failed"
  let some (.pair left right) := (read root store.memory).value |
    throw <| IO.userError "nested data pair is missing"
  unless (readWord store.memory right).value == some (natBits 24 4) do
    throw <| IO.userError "nested Fin data was truncated"
  let some (.cons head tail) := (read left store.memory).value |
    throw <| IO.userError "nested list head is missing"
  let some (.pair flag value) := (read head store.memory).value |
    throw <| IO.userError "nested list element is missing"
  unless (readBool store.memory flag).value == some true &&
      (readWord store.memory value).value == some (natBits 24 2) do
    throw <| IO.userError "nested list values changed"
  let some (.cons _ nilRoot) := (read tail store.memory).value |
    throw <| IO.userError "nested list tail is missing"
  unless (read nilRoot store.memory).value == some .nil &&
      (readWord store.memory initial.value.1).value == some (natBits 24 0) do
    throw <| IO.userError "data loading broke an old root or list termination"
  unless out.steps ≤ (nested.load nestedValue).steps*HeapData.factor 24 (1+(nested.load nestedValue).steps) do
    throw <| IO.userError "nested data load exceeded its complete bit-step bound"

#eval show IO Unit from do
  for w in List.range 7 do
    for n in [1, 2, 3, 4, 5, 8, 16, 32] do
      if n ≤ 2^w then
        let v := PaddedSampling.width n w
        for k in List.range 3 do
          for t in List.range (2^(v*k)) do
            let tape := natBits (v*k) t
            let (out, rest) := (simulateQ tapeOracle (PaddedSampling.run (PaddedSampling.compile n w k))).run tape
            let (expected, unused) := expectedSample n v k tape
            unless out.value.1 == natBits w expected.1 && out.value.2 == expected.2 && rest == unused do
              throw <| IO.userError "padded sampler changed the value, flag, or consumed prefix"
            unless out.steps ≤ PaddedSampling.budget n w k do
              throw <| IO.userError "padded sampler exceeded its CPU bound"

#eval show IO Unit from do
  let compiled := HeapMachine.compileBody 24 3 curve curve 2 code
  let factor := HeapProgram.budget 24 21 (HeapMachine.fee 24 3 2 21) code
  for t in List.range 1024 do
    let tape := natBits 10 t
    let (scalar, rest) := expectedSample 3 2 2 tape
    let (uniform, unused) := expectedSample 5 3 2 rest
    for alreadyBad in [false, true] do
      let ((out, state), remaining) :=
        (simulateQ tapeOracle ((compiled.run HeapMachine.Instruction.run [] initial.value.2).run
          (initial.value.1, alreadyBad))).run tape
      let some (root, heap) := out.value | throw <| IO.userError "closed machine failed to return a heap value"
      unless (readWord heap.memory root).value == some (natBits 24 uniform.1) && state.1 == root do
        throw <| IO.userError "write/read failed to preserve the sampled typed value"
      unless state.2 == (alreadyBad || scalar.2 || uniform.2) && remaining == unused do
        throw <| IO.userError "machine lost its sticky failure flag or consumed the wrong bits"
      unless heap.count.length == 7 && (readWord heap.memory initial.value.1).value == some (natBits 24 0) do
        throw <| IO.userError "machine heap allocation or old-root preservation mismatch"
      unless out.steps ≤ 20*factor do
        throw <| IO.userError "precompiled machine exceeded its full body budget"

example : PaddedSampling.width 8 3 = 3 := rfl

#eval show IO Unit from do
  let compiled := HeapMachine.compile 24 3 curve curve 2 closed
  let factor := HeapMachine.budget 24 3 2 24 closed
  for t in List.range 1024 do
    let tape := natBits 10 t
    let (scalar, rest) := expectedSample 3 2 2 tape
    let (uniform, unused) := expectedSample 5 3 2 rest
    let ((out, bad), remaining) := (simulateQ tapeOracle (compiled.run [] empty)).run tape
    let some (root, heap) := out.value | throw <| IO.userError "machine initialization failed"
    unless (readWord heap.memory root).value == some (natBits 24 uniform.1) &&
        bad == (scalar.2 || uniform.2) && remaining == unused do
      throw <| IO.userError "initialized machine changed its value, failure flag, or bit prefix"
    unless heap.count.length == 8 && out.steps ≤ 24*factor do
      throw <| IO.userError "initialization was omitted from allocation or bit-step accounting"

example : ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool)
    (PaddedSampling.run (PaddedSampling.compile 8 3 1))).map (fun out => out.value.2)) true = 0 := by
  rw [PaddedSampling.bad_eq 8 3 1 (by decide)]
  have h : PaddedSampling.width 8 3 = 3 := rfl
  rw [h]
  norm_num [ENNReal.mul_inv_cancel]

end SignaturesTest.HeapMachine

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``PaddedSampling.run_support, ``PaddedSampling.run_queries,
      ``PaddedSampling.distribution, ``PaddedSampling.bad_eq, ``PaddedSampling.bad_le,
      ``HeapProgram.Code.run_mapQueries, ``QueryTreeRel.refl,
      ``HeapMachine.handler_costed, ``HeapMachine.semantics_bound, ``HeapMachine.semantics_support,
      ``Program.run_support_refines,
      ``HeapMachine.compileBody_costed, ``HeapMachine.codeSemantics_support,
      ``HeapMachine.compile_costed, ``HeapData.encode_spec, ``HeapData.encode_steps,
      ``HeapData.encodeEnv_costed, ``HeapMachine.budget_mono,
      ``HeapMachine.packageSemantics_support, ``HeapMachine.compilePackage_costed] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
