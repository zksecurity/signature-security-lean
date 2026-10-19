import Signatures.Runtime.Caliper.BLSFullReduction

/-! Exact source equality of both complete generated Caliper programs. Only the
caller's local machine semantics and erasure to the algebraic adversary remain
parameters; setup, the shared lazy cache and extraction are implemented here. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G K A : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
    [AddCommGroup G] [Module (val.Value base) G] [AddCommGroup K] [Module (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout) (fuel : Nat)
    (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Caller.Invariant layout caller fuel)
    (witness : Caller.Correspondence layout caller invariant)
    (adversary : Model.LazyAGM.Adversary (val.Value base) (key.Value base) (key.Value base) G K)
    (same : ∀ pk : layout.key.Value, (fun answer => output answer.val) <$> witness.source pk.val = adversary.main pk.val)
    (logRoom : fuel ≤ layout.tokens.capacity) (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1)

include drawLaw same logRoom cacheRoom in
theorem good_source (value : layout.setup.challenge.Value) :
    Subtype.val <$> goodSource layout routines P comparison correct caller fuel drawSource value =
      BLS.LazyAGM.Reduction.goodReductionList adversary value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 := by
  change Subtype.val <$> goodTailSource layout routines P comparison correct caller fuel drawSource (goodStart layout value) = _
  rw [good_tail_original layout routines P comparison correct caller fuel drawSource drawLaw invariant witness
    (goodStart layout value) (good_start_admitted layout fuel logRoom cacheRoom value)]
  exact good_original_finish Subtype.val (witness.source (goodStart layout value).1.val) adversary
    value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 (same (goodStart layout value).1)

include drawLaw same logRoom cacheRoom in
theorem bad_source (value : layout.setup.challenge.Value) :
    Subtype.val <$> badSource layout routines P comparison correct caller fuel drawSource value =
      BLS.LazyAGM.Reduction.badReductionList adversary value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 := by
  change Subtype.val <$> (badStart layout routines drawSource value >>= badTailSource layout routines P comparison correct caller fuel drawSource) = _
  rw [map_bind]
  have tail : (badStart layout routines drawSource value >>= fun started =>
      Subtype.val <$> badTailSource layout routines P comparison correct caller fuel drawSource started) =
    (badStart layout routines drawSource value >>= fun started =>
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
        (BLS.LazyAGM.Reduction.badProgram value.val.1.1 value.val.1.2 started.1.val started.2.val.1.1 adversary)).run' []) := by
    apply bind_congr_of_forall_mem_support
    intro started reached
    rw [bad_tail_original layout routines P comparison correct caller fuel drawSource drawLaw invariant witness started
      (bad_start_admitted layout routines drawSource fuel logRoom cacheRoom value started reached)]
    unfold badStart BLSSetup.badSource at reached
    erw [support_map] at reached
    obtain ⟨result, resultReached, rfl⟩ := reached
    erw [support_map] at resultReached
    obtain ⟨scalar, _, rfl⟩ := resultReached
    exact bad_original_finish Subtype.val _ adversary value.val.1.1 value.val.1.2 _
      (same (layout.badSetupView (BLSSetup.badResult layout.setup routines.keyScale routines.keyNames.buffers
        (by have := routines.reserve; omega) (BLSSetup.sampledValue layout.setup value scalar))).1) scalar.val
  rw [tail]
  unfold badStart BLSSetup.badSource
  simp only [bind_map_left]
  rw [BLS.LazyAGM.Reduction.badReductionList, ← drawLaw, bind_map_left]
  erw [bind_map_left]
  rfl

variable (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines layout.port .unit layout.scheme.cache.lookup.unit.representation
      layout.scheme.cache.value.representation (fun _ => drawSource) draw)

include drawCorrect drawLaw same logRoom cacheRoom in
theorem good_observe_original (tape : RandomTape w) (value : layout.setup.challenge.Value)
    (before : State w) (holds : layout.setup.challenge.representation.Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.scheme.cache.value.representation finished) <$>
        (goodCode layout routines P comparison correct caller draw fuel).execute layout.port .unit tape before =
      some <$> BLS.LazyAGM.Reduction.goodReductionList adversary value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 := by
  have observed := (good_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant logRoom cacheRoom).observe tape value before holds
  have erased := congrArg (fun computation => (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← good_source layout routines P comparison correct caller fuel drawSource drawLaw invariant witness adversary same logRoom cacheRoom value]
  have middle : (fun answer => Subtype.val <$> answer) <$> some <$>
      goodSource layout routines P comparison correct caller fuel drawSource value =
        some <$> Subtype.val <$> goodSource layout routines P comparison correct caller fuel drawSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (erased.trans middle)

include drawCorrect drawLaw same logRoom cacheRoom in
theorem bad_observe_original (tape : RandomTape w) (value : layout.setup.challenge.Value)
    (before : State w) (holds : layout.setup.challenge.representation.Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.scheme.cache.value.representation finished) <$>
        (badCode layout routines P comparison correct caller draw fuel).execute layout.port .unit tape before =
      some <$> BLS.LazyAGM.Reduction.badReductionList adversary value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 := by
  have observed := (bad_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant logRoom cacheRoom).observe tape value before holds
  have erased := congrArg (fun computation => (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← bad_source layout routines P comparison correct caller fuel drawSource drawLaw invariant witness adversary same logRoom cacheRoom value]
  have middle : (fun answer => Subtype.val <$> answer) <$> some <$>
      badSource layout routines P comparison correct caller fuel drawSource value =
        some <$> Subtype.val <$> badSource layout routines P comparison correct caller fuel drawSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (erased.trans middle)
end Signatures.Runtime.CaliperBackend.BLSFull
