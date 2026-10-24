import Proofs.Runtime.Caliper.CompositionAcceptance

/-! Constructive acceptance rules for original expression certificates.
The witness is returned by the existing checked compiler, with a proved bound
on its buffer names. No replacement compiler or assumed successful run is used. -/

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    {P : Primitives base Op} {hw : 16 < 2 ^ w}

def Compilation.Emits {Γ : List (Ty Atom)} {a : Ty Atom} {expression : Expr Op Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P .unit hw expression input output) (buffers : Nat) : Prop :=
  ∃ implementation, certificate.compile (by decide) = some implementation ∧ implementation.program.code.memBound ≤ buffers

theorem Compilation.Emits.mono {Γ : List (Ty Atom)} {a : Ty Atom} {expression : Expr Op Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    {certificate : Compilation P .unit hw expression input output} {buffers larger : Nat}
    (emitted : certificate.Emits buffers) (bound : buffers ≤ larger) : certificate.Emits larger := by
  obtain ⟨implementation, accepted, names⟩ := emitted
  exact ⟨implementation, accepted, names.trans bound⟩

theorem Compilation.Emits.isSome {Γ : List (Ty Atom)} {a : Ty Atom} {expression : Expr Op Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    {certificate : Compilation P .unit hw expression input output} {buffers : Nat}
    (emitted : certificate.Emits buffers) : (certificate.compile (by decide)).isSome := by
  obtain ⟨implementation, accepted, _⟩ := emitted
  simp only [accepted, Option.isSome_some]

theorem Compilation.Emits.buffers {Γ : List (Ty Atom)} {a : Ty Atom} {expression : Expr Op Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    {certificate : Compilation P .unit hw expression input output} {buffers : Nat}
    (emitted : certificate.Emits buffers) (implementation : Implementation .unit input output (expression.denote P))
    (accepted : certificate.compile (by decide) = some implementation) : implementation.program.code.memBound ≤ buffers := by
  obtain ⟨body, bodyEq, bound⟩ := emitted
  rw [Option.some.inj (accepted.symm.trans bodyEq)]
  exact bound

theorem Compilation.Emits.var {Γ : List (Ty Atom)} {a : Ty Atom} {v : Var Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (access : Variable v input output) :
    (Compilation.var (P := P) (cost := .unit) (hw := hw) access).Emits 2 :=
  ⟨access.compile (by decide) hw, rfl, access.buffers (by decide) hw⟩

theorem Compilation.Emits.bool {Γ : List (Ty Atom)} (input : Layout w (Env base Γ)) (value : Bool) :
    (Compilation.bool (P := P) (cost := .unit) (hw := hw) (Γ := Γ) input value).Emits 2 :=
  ⟨DataImplementation.boolean .unit (by decide) input value hw, rfl,
    DataImplementation.boolean_buffers (by decide) input value hw⟩

theorem Compilation.Emits.fst {Γ : List (Ty Atom)} {a b : Ty Atom} {value : Expr Op Γ (.pair a b)}
    {input : Layout w (Env base Γ)} (left : Layout w (a.Value base)) (right : Layout w (b.Value base))
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {code : Compilation P .unit hw value input (left.prod right fits)} {buffers : Nat}
    (emitted : code.Emits buffers) : (Compilation.fst (P := P) (cost := .unit) (hw := hw) (Γ := Γ) (a := a) (b := b) left right fits code).Emits (max buffers 2) := by
  obtain ⟨body, accepted, bound⟩ := emitted
  refine ⟨body.then (Implementation.first (by decide) left right hw fits), ?_,
    max_le_max bound (Implementation.first_buffers (by decide) left right hw fits)⟩
  dsimp only [Compilation.compile]
  rw [accepted]
  rfl

theorem Compilation.Emits.snd {Γ : List (Ty Atom)} {a b : Ty Atom} {value : Expr Op Γ (.pair a b)}
    {input : Layout w (Env base Γ)} (left : Layout w (a.Value base)) (right : Layout w (b.Value base))
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {code : Compilation P .unit hw value input (left.prod right fits)} {buffers : Nat}
    (emitted : code.Emits buffers) : (Compilation.snd (P := P) (cost := .unit) (hw := hw) (Γ := Γ) (a := a) (b := b) left right fits code).Emits (max buffers 2) := by
  obtain ⟨body, accepted, bound⟩ := emitted
  refine ⟨body.then (Implementation.second (by decide) left right hw fits), ?_,
    max_le_max bound (Implementation.second_buffers (by decide) left right hw fits)⟩
  dsimp only [Compilation.compile]
  rw [accepted]
  rfl

theorem Compilation.Emits.op {Γ : List (Ty Atom)} {a b : Ty Atom} (instruction : Op a b)
    {value : Expr Op Γ a} {input : Layout w (Env base Γ)} {argument : Layout w (a.Value base)} {output : Layout w (b.Value base)}
    (implementation : Implementation .unit argument output (P.execute instruction))
    {code : Compilation P .unit hw value input argument} {buffers primitiveBuffers : Nat}
    (emitted : code.Emits buffers) (primitiveBound : implementation.program.code.memBound ≤ primitiveBuffers) :
    (Compilation.op (P := P) (cost := .unit) (hw := hw) (Γ := Γ) (a := a) (b := b) instruction implementation code).Emits (max buffers primitiveBuffers) := by
  obtain ⟨body, accepted, bound⟩ := emitted
  refine ⟨body.then implementation, ?_, max_le_max bound primitiveBound⟩
  dsimp only [Compilation.compile]
  rw [accepted]
  rfl

theorem Compilation.Emits.pair {Γ : List (Ty Atom)} {a b : Ty Atom} {first : Expr Op Γ a} {second : Expr Op Γ b}
    {input : Layout w (Env base Γ)} {left : Layout w (a.Value base)} {right : Layout w (b.Value base)}
    {firstCode : Compilation P .unit hw first input left} {secondCode : Compilation P .unit hw second input right}
    {firstBuffers secondBuffers : Nat} (firstEmitted : firstCode.Emits firstBuffers) (secondEmitted : secondCode.Emits secondBuffers)
    (firstFits : firstBuffers < 2 ^ w) (secondFits : secondBuffers < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (Compilation.pair (P := P) (cost := .unit) (hw := hw) (Γ := Γ) (a := a) (b := b) firstCode secondCode duplicateFits middleFits outputFits).Emits (max 2 (max firstBuffers secondBuffers) + 1) := by
  obtain ⟨left, leftEq, leftBound⟩ := firstEmitted
  obtain ⟨right, rightEq, rightBound⟩ := secondEmitted
  obtain ⟨paired, pairedEq, pairedBound⟩ := left.checkedPair_accept right (by decide) hw leftBound rightBound
    firstFits secondFits duplicateFits middleFits outputFits
  refine ⟨paired, ?_, pairedBound⟩
  dsimp only [Compilation.compile]
  rw [leftEq, rightEq]
  exact pairedEq

theorem Compilation.Emits.branch {Γ : List (Ty Atom)} {a : Ty Atom}
    {condition : Expr Op Γ .bool} {yes no : Expr Op Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    {test : Compilation P .unit hw condition input (DataImplementation.boolLayout w (width_pos hw))}
    {left : Compilation P .unit hw yes input output} {right : Compilation P .unit hw no input output}
    {testBuffers leftBuffers rightBuffers : Nat}
    (testEmitted : test.Emits testBuffers) (leftEmitted : left.Emits leftBuffers) (rightEmitted : right.Emits rightBuffers)
    (testFits : testBuffers < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w) :
    (Compilation.branch (P := P) (cost := .unit) (hw := hw) (Γ := Γ) (a := a) test left right duplicateFits tagFits).Emits (max (max 2 testBuffers + 1) (max leftBuffers rightBuffers)) := by
  obtain ⟨test, testEq, testBound⟩ := testEmitted
  obtain ⟨left, leftEq, leftBound⟩ := leftEmitted
  obtain ⟨right, rightEq, rightBound⟩ := rightEmitted
  obtain ⟨branched, branchedEq, branchedBound⟩ := test.checkedBranch_accept left right (by decide)
    testBound leftBound rightBound testFits duplicateFits tagFits
  refine ⟨branched, ?_, branchedBound⟩
  dsimp only [Compilation.compile]
  rw [testEq, leftEq, rightEq]
  exact branchedEq

end Signatures.Runtime.CaliperBackend.SourceExpression
