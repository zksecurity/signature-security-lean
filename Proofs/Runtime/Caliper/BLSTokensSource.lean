import Proofs.Runtime.Caliper.BLSTokensOracle
import Proofs.Runtime.LazyAGMExtraction

/-! The constructed evaluator implements the evalTerms computation used in
the source BLS reduction, with chronological coefficient matching and the
entire private cache preserved. Source field algebra does not justify a free
implementation: the code and its bounds come from the preceding modules. -/
namespace Signatures.Runtime.CaliperBackend.BLSTokens
open Caliper BoundedSource OracleComp OracleSpec

theorem rows_terms {F M G : Type} [Zero F] (tokens : List (M × G)) (coefficients : List F) :
    (tokens.reverse.mapIdx (fun n token => (token, (coefficients[n]?).getD 0))).map (fun row => (row.1.1, row.2)) =
      BLS.LazyAGM.Reduction.traceTerms coefficients tokens.reverse := by
  simp [BLS.LazyAGM.Reduction.traceTerms, Model.LazyAGM.tokenCoeff,
    List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def]

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
    (layout : Layouts w (key.Value base) G (val.Value base))
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (addBuffers : add.program.code.memBound ≤ slots)
    (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include uniform in
theorem good_source (value : layout.good.input.Value) (ready : layout.good.ready value) :
    Subtype.val <$> goodDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source value =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
        (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2 value.val.1.1.reverse))).run value.val.2 := by
  rw [good_privateOracle layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source uniform value ready]
  have folded := LazyAGM.foldRows_simulate (F := val.Value base)
    (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
    (value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD 0))) 0
  rw [rows_terms] at folded
  convert congrArg (fun computation => computation.run value.val.2) folded using 1
  simp only [zero_add, id_map']

include uniform in
theorem bad_source (value : layout.bad.input.Value) (ready : layout.bad.ready value) :
    Subtype.val <$> badDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source value =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
        (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2 value.val.1.1.reverse))).run value.val.2 := by
  rw [bad_privateOracle layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source uniform value ready]
  have folded := LazyAGM.foldRows_simulate (F := val.Value base)
    (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
    (value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD 0))) 0
  rw [rows_terms] at folded
  convert congrArg (fun computation => computation.run value.val.2) folded using 1
  simp only [zero_add, id_map']
end Signatures.Runtime.CaliperBackend.BLSTokens
