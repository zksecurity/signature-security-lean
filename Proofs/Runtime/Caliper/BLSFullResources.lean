import Proofs.Runtime.Caliper.BLSFullAcceptance

/-! Full-program memory accounting for the same supported source/output execution.
Stored code, initial challenge data, scratch descriptors and every intermediate
buffer state are charged, including setup and both terminal paths. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G K A : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout) (draw : Interactive.Code w) (fuel : Nat)
    (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawCorrect : Interactive.Refines layout.port .unit layout.scheme.cache.lookup.unit.representation
      layout.scheme.cache.value.representation (fun _ => drawSource) draw)
    (bound : Routines.Bounds layout routines) (localBound : Caller.Bounds layout caller)
    {drawTime drawWords : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.scheme.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)

variable [SampleableType (val.Value base)]
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Caller.Invariant layout caller fuel)
    (logRoom : fuel ≤ layout.tokens.capacity) (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1)
    {drawNames : Nat} (drawNamed : WordIO.NamesBound (draw.lower layout.port) drawNames)

include drawCorrect drawLaw invariant drawTimeBound drawWordsBound logRoom cacheRoom drawNamed in
theorem good_resources (tape : RandomTape w) (value : layout.setup.challenge.Value) (before : State w)
    (holds : layout.setup.challenge.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((goodCode layout routines P comparison correct caller draw fuel).execute layout.port .unit tape before)) :
    let code := goodCode layout routines P comparison correct caller draw fuel
    let time := goodTime layout routines bound caller localBound drawTime fuel
    let words := goodWords layout routines bound caller localBound drawWords fuel
    let names := nameBudget layout routines caller localBound drawNames
    finished.time ≤ time ∧ ∃ answer ∈ support (goodSource layout routines P comparison correct caller fuel drawSource value),
      layout.scheme.cache.value.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower layout.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower layout.port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower layout.port).memBound) ∧ between.WellFormed ∧
          ((code.lower layout.port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower layout.port).memBound) ≤
            5 * words + 4 * names + registers + 3 * buffers + before.liveMem buffers + time := by
  have refined := good_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant logRoom cacheRoom
  have timed := good_time layout routines P comparison correct caller draw fuel drawSource drawCorrect bound localBound drawTimeBound drawLaw invariant logRoom cacheRoom
  have stored := good_words layout routines P comparison correct caller draw fuel bound localBound drawWordsBound
  have named := good_names layout routines P comparison correct caller draw fuel localBound drawNamed
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources timed stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
    tape value before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩

include drawCorrect drawLaw invariant drawTimeBound drawWordsBound logRoom cacheRoom drawNamed in
theorem bad_resources (tape : RandomTape w) (value : layout.setup.challenge.Value) (before : State w)
    (holds : layout.setup.challenge.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((badCode layout routines P comparison correct caller draw fuel).execute layout.port .unit tape before)) :
    let code := badCode layout routines P comparison correct caller draw fuel
    let time := badTime layout routines bound caller localBound drawTime fuel
    let words := badWords layout routines bound caller localBound drawWords fuel
    let names := nameBudget layout routines caller localBound drawNames
    finished.time ≤ time ∧ ∃ answer ∈ support (badSource layout routines P comparison correct caller fuel drawSource value),
      layout.scheme.cache.value.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower layout.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower layout.port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower layout.port).memBound) ∧ between.WellFormed ∧
          ((code.lower layout.port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower layout.port).memBound) ≤
            5 * words + 4 * names + registers + 3 * buffers + before.liveMem buffers + time := by
  have refined := bad_refines layout routines P comparison correct caller draw fuel drawSource drawCorrect drawLaw invariant logRoom cacheRoom
  have timed := bad_time layout routines P comparison correct caller draw fuel drawSource drawCorrect bound localBound drawTimeBound drawLaw invariant logRoom cacheRoom
  have stored := bad_words layout routines P comparison correct caller draw fuel bound localBound drawWordsBound
  have named := bad_names layout routines P comparison correct caller draw fuel localBound drawNamed
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources timed stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
    tape value before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩
end Signatures.Runtime.CaliperBackend.BLSFull
