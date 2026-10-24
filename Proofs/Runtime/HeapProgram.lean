import Proofs.Runtime.HeapArguments
import Proofs.Runtime.HeapLoop

/-! First-order program compilation to the shared bit-tape backend. Query
handlers receive heap roots, not decoded semantic values. Semantic/allocation
refinement is in HeapProgramCorrectness; aggregate bit-step bounds are in
HeapProgramCost. Concrete handler/sampling implementations remain separate
obligations. -/

namespace Signatures.Runtime.HeapProgram

open HeapBits SharedHeap WeierstrassCurve

abbrev HandlerM (Cmd : Ty CryptoAtom → Ty CryptoAtom → Type) (m : Type → Type) :=
  {a b : Ty CryptoAtom} → Cmd a b → Address → Store → m (Run HeapExpression.Result)

inductive Code (Cmd : Ty CryptoAtom → Ty CryptoAtom → Type) where
  | ret (value : HeapExpression.Code)
  | query {a b : Ty CryptoAtom} (cmd : Cmd a b) (arg : HeapExpression.Code)
  | bind (first body : Code Cmd)
  | branch (cond : HeapExpression.Code) (yes no : Code Cmd)
  | loop (count init : HeapExpression.Code) (body : Code Cmd)
  | call (body : Code Cmd) (args : List HeapExpression.Code)

def bindM {m : Type → Type} [Monad m] {A B : Type}
    (first : m (Run (Option A))) (next : A → m (Run (Option B))) : m (Run (Option B)) := do
  let r ← first
  match r.value with
  | none => pure ⟨none, r.steps + 1⟩
  | some a =>
    let s ← next a
    pure ⟨s.value, r.steps + s.steps + 1⟩

def Code.run {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type} {m : Type → Type} [Monad m]
    (H : HandlerM Cmd m) : Code Cmd → List Bool → Store → m (Run HeapExpression.Result)
  | .ret value, frame, store =>
    let out := value.run frame store
    pure ⟨out.value, out.steps + 1⟩
  | .query cmd arg, frame, store =>
    bindM (pure (arg.run frame store)) fun p => H cmd p.1 p.2
  | .bind first body, frame, store =>
    bindM (first.run H frame store) fun p => do
      let next := framePush p.1 frame
      let out ← body.run H next.value p.2
      pure ⟨out.value, next.steps + out.steps + 1⟩
  | .branch cond yes no, frame, store =>
    bindM (pure (cond.run frame store)) fun p =>
      bindM (pure (readBool p.2.memory p.1)) fun b =>
        if b then yes.run H frame p.2 else no.run H frame p.2
  | .loop count init body, frame, store =>
    bindM (pure (count.run frame store)) fun p =>
      bindM (pure (init.run frame p.2)) fun q =>
        bindM (pure (readWord q.2.memory p.1)) fun bits =>
          HeapLoop.run (fun root heap => do
            let next := framePush root frame
            let out ← body.run H next.value heap
            pure ⟨out.value, next.steps + out.steps + 1⟩) bits q.1 q.2
  | .call body args, frame, store =>
    bindM (pure (HeapArguments.run args frame store)) fun p => do
      let out ← body.run H p.1 p.2
      pure ⟨out.value, out.steps + 1⟩

def compile {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type} {p₁ p₂ : Nat}
    (w r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} : Program CryptoOp Cmd Γ a → Code Cmd
  | .ret value => .ret (HeapExpression.compile w r W₁ W₂ value)
  | .query cmd arg => .query cmd (HeapExpression.compile w r W₁ W₂ arg)
  | .bind first body => .bind (compile w r W₁ W₂ first) (compile w r W₁ W₂ body)
  | .branch cond yes no => .branch (HeapExpression.compile w r W₁ W₂ cond)
      (compile w r W₁ W₂ yes) (compile w r W₁ W₂ no)
  | .loop count init body => .loop (HeapExpression.compile w r W₁ W₂ count)
      (HeapExpression.compile w r W₁ W₂ init) (compile w r W₁ W₂ body)
  | .call body args => .call (compile w r W₁ W₂ body) (HeapArguments.compile w r W₁ W₂ args)

/-- Replace static effect instructions before execution, including inside loops. -/
def Code.mapQueries {Cmd Target : Ty CryptoAtom → Ty CryptoAtom → Type}
    (f : {a b : Ty CryptoAtom} → Cmd a b → Target a b) : Code Cmd → Code Target
  | .ret e => .ret e
  | .query cmd e => .query (f cmd) e
  | .bind first body => .bind (first.mapQueries f) (body.mapQueries f)
  | .branch cond yes no => .branch cond (yes.mapQueries f) (no.mapQueries f)
  | .loop count init body => .loop count init (body.mapQueries f)
  | .call body args => .call (body.mapQueries f) args

theorem Code.run_mapQueries {Cmd Target : Ty CryptoAtom → Ty CryptoAtom → Type}
    {m : Type → Type} [Monad m] (f : {a b : Ty CryptoAtom} → Cmd a b → Target a b)
    (H : HandlerM Target m) (code : Code Cmd) (frame : List Bool) (store : Store) :
    (code.mapQueries f).run H frame store = code.run (fun cmd => H (f cmd)) frame store := by
  induction code generalizing frame store <;> simp only [mapQueries, run, *]

end Signatures.Runtime.HeapProgram
