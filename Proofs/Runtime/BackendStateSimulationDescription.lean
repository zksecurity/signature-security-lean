import Proofs.Runtime.BackendStateSimulation
import Proofs.Runtime.BackendDescriptionLaws

/-! Stored-code overhead of state-passing simulation. Each original query node
stores one handler; loops keep one body and never enumerate their inputs. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)

include laws

omit QD in
theorem shuffle_description {A E T : Type} (a : C.Str A) (e : C.Str E) (t : C.Str T) :
    sizes.localSize (shuffle (Q := Q) a e t) ≤ 9 * allowance := by
  exact (laws.pair_bound
    (laws.pair_bound (laws.compose_bound (laws.fst _ _) (laws.fst _ _)) (laws.snd _ _))
    (laws.compose_bound (laws.fst _ _) (laws.snd _ _))).trans (by omega)

omit QD in
theorem associate_description {A E T : Type} (a : C.Str A) (e : C.Str E) (t : C.Str T) :
    sizes.localSize (associate (Q := Q) a e t) ≤ 9 * allowance := by
  exact (laws.pair_bound (laws.compose_bound (laws.fst _ _) (laws.fst _ _))
    (laws.pair_bound (laws.compose_bound (laws.fst _ _) (laws.snd _ _)) (laws.snd _ _))).trans
      (by omega)

variable {I J S : Type} {source : OracleSpec I} {target : OracleSpec J}
  {src : Interface (C := C) source} {dst : Interface (C := C) target}
  (store : C.Str S)
  (handler : Code Q target dst (StepClass.HasProd.prod src.position store)
    (StepClass.HasProd.prod src.response store))

theorem compile_description
    (distribute : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T),
      sizes.localSize (QD.distribute a b t) ≤ allowance)
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q source src a b) :
    (compile store handler program).descriptionSize sizes ≤
      (handler.descriptionSize sizes + 18 * allowance + 6) * program.descriptionSize sizes := by
  induction program with
  | atomic code => simp only [compile, Code.descriptionSize]; nlinarith
  | query => simp only [compile, Code.descriptionSize]; omega
  | seq initial following hi hf =>
      simp only [compile, Code.descriptionSize] at *
      nlinarith
  | @branch A B D a b d left right hl hr =>
      have hd := distribute a b store
      simp only [compile, Code.descriptionSize] at *
      nlinarith
  | @first A B T a b retained body ih =>
      have hin := shuffle_description sizes allowance laws a retained store
      have hout := shuffle_description sizes allowance laws b store retained
      simp only [compile, Code.descriptionSize] at *
      nlinarith
  | @loop A B a b body stop fuel hb hs =>
      have hd := distribute b a store
      simp only [compile, Code.descriptionSize] at *
      nlinarith
  | @iterate A a counter body ih =>
      have hi := associate_description sizes allowance laws counter a store
      simp only [compile, Code.descriptionSize] at *
      nlinarith

end Signatures.Runtime.BackendProgram.StateSimulation
