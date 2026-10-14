import Signatures.Schnorr.Statement
import Signatures.Schnorr.BitStatement
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrReduction

variable {F G M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

private def returnForgery : Program CryptoOp (Command 0) [point₁, forgery] forgery :=
  .ret (.var (.there .here))

private def fixedAdversary (g : G) (value : M × G × F) :
    _root_.Schnorr.ROM.Adversary (F := F) (M := M) g where
  main _ := pure value

private def fixedCertificate (g : G) (value : M × G × F) :
    SourceCertificate (G₂ := G) (K := M) PrimitiveCosts.unit 0 3 (fun _ => 0)
      (fixedAdversary g value).main where
  dataTy := forgery
  data := value
  code := returnForgery
  semantics _ := rfl
  budget pk := by
    intro price result hr
    simp only [returnForgery, Program.run, Expr.run, Var.get, Var.depth, support_pure,
      Set.mem_singleton_iff] at hr
    have hsteps := congrArg Run.steps hr
    change result.steps = 3 at hsteps
    simpa only [Nat.zero_mul, Finset.sum_const_zero, Nat.add_zero] using hsteps.le

attribute [local irreducible] Machine.Code.run Machine.Package.run

-- Simplifying the public budget must retain unary loading of qH and all fixed data.
example (g : G) (value : M × G × F) (sampling : Machine.SamplingCosts) (qH : Nat) :
    (fixedCertificate g value).targetBudget sampling qH =
      forkPrice PrimitiveCosts.unit sampling 0 3 (fun _ => 0) + qH + 14 := by
  simp [SourceCertificate.targetBudget, fixedCertificate, forgery, Ty.load]
  omega

-- Even a zero-query adversary executes the final verification query and full fork controller.
example (g : G) (value : M × G × F) (sampling : Machine.SamplingCosts) :
    dlogWithin (G₂ := G) (K := M) (M := M) PrimitiveCosts.unit sampling g
      ((fixedCertificate g value).targetBudget sampling 0)
      (_root_.Schnorr.dlogReduction F G g M (fixedAdversary g value) 0) :=
  (fixedCertificate g value).within sampling g 0

-- This is query-tree equality, not merely equality of success probabilities.
example (g pk : G) (value : M × G × F) (sampling : Machine.SamplingCosts) :
    Run.value <$> (forkCode 0 returnForgery).run (G₂ := G) (K := M)
      PrimitiveCosts.unit sampling (pk, g, 0, value, ()) =
      _root_.Schnorr.dlogReduction F G g M (fixedAdversary g value) 0 g pk :=
  (fixedCertificate g value).reduction sampling g pk 0

private def adaptiveSource : Program CryptoOp (Command 0) [point₁, message] forgery :=
  .bind (.query .sign (.var (.there .here)))
    (.bind (.query .hash (.pair (.var (.there (.there .here))) (.fst (.var .here))))
      (.ret (.pair (.var (.there (.there (.there .here))))
        (.pair (.fst (.var (.there .here))) (.var .here)))))

private def adaptiveAdversary (g : G) (msg : M) :
    _root_.Schnorr.ROM.Adversary (F := F) (M := M) g where
  main _ := do
    let signed ← (FiatShamir.cmaOracleSpec M G F F).query (.inr msg)
    let c ← (FiatShamir.cmaOracleSpec M G F F).query (.inl (.inr (msg, signed.1)))
    pure (msg, signed.1, c)

private def adaptiveQueries (i : Fin 3) : Nat := if i = 0 then 0 else 1

private def adaptiveCertificate (g : G) (msg : M) :
    SourceCertificate (G₂ := G) (K := M) PrimitiveCosts.unit 0 32 adaptiveQueries
      (adaptiveAdversary (F := F) g msg).main where
  dataTy := message
  data := msg
  code := adaptiveSource
  semantics _ := rfl
  budget pk := by
    intro price result hr
    simp only [adaptiveSource, Program.run, Expr.run, Var.get, Var.depth, pricedRequests,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨a, ha, r, hr, rfl⟩ := hr
    obtain ⟨b, hb, r, hr, rfl⟩ := hr
    obtain ⟨c, _, rfl⟩ := hr
    obtain ⟨x, ⟨u, _, rfl⟩, rfl⟩ := ha
    obtain ⟨y, ⟨v, _, rfl⟩, rfl⟩ := hb
    simp [kind, adaptiveQueries, Fin.sum_univ_succ]
    omega

-- The hash input depends on a previous signing reply; resources cover every such reply.
example (g : G) (msg : M) (sampling : Machine.SamplingCosts) :
    dlogWithin (G₂ := G) (K := M) (M := M) PrimitiveCosts.unit sampling g
      ((adaptiveCertificate (F := F) g msg).targetBudget sampling 1)
      (_root_.Schnorr.dlogReduction F G g M (adaptiveAdversary g msg) 1) :=
  (adaptiveCertificate (F := F) g msg).within sampling g 1

end SignaturesTest.SchnorrReduction

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Signatures.Runtime.Replay.contextFork_map,
      ``Signatures.Runtime.Replay.contextFork_outputs,
      ``source_refines, ``macroPass_valid, ``SourceCertificate.trace,
      ``expandedFork_extract, ``SourceCertificate.reduction, ``SourceCertificate.within,
      ``SourceCertificate.bitCode_costed, ``SourceCertificate.bitCode_error,
      ``Schnorr.Statement.schnorr_eufcma_of_dlog_bit_hardness,
      ``Schnorr.Statement.schnorr_eufcma_of_dlog_machine_hardness] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
  let endpoint := ``Schnorr.Statement.schnorr_eufcma_of_dlog_machine_hardness
  let axioms ← collectAxioms endpoint
  unless #[``propext, ``Classical.choice, ``Quot.sound].all axioms.contains do
    throwError "{endpoint}: changed axiom footprint {axioms}"
