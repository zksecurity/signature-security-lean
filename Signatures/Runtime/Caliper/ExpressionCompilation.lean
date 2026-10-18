import Signatures.Runtime.Caliper.ExpressionCertificate

/-! Checked compilation of original source expressions. A successful result
contains literal Caliper code, a source-result proof, preserved capacity bounds,
and execution profiles. No implementation of a finished expression is assumed. -/

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    {P : Primitives base Op} {cost : CostModel} {hw : 16 < 2 ^ w}

def Compilation.compile (allocation : 1 ≤ cost.allocPerWord) {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)} :
    Compilation P cost hw expression input output → Option (Implementation cost input output (expression.denote P))
  | .var access => some (access.compile allocation hw)
  | .unit input => some (DataImplementation.unit cost allocation input hw)
  | .bool input value => some (DataImplementation.boolean cost allocation input value hw)
  | .nat input value bound fits valid => some (Natural.constant cost allocation input bound value hw fits valid)
  | .pair first second duplicateFits middleFits outputFits => do
      let left ← first.compile allocation
      let right ← second.compile allocation
      left.checkedPair right allocation hw duplicateFits middleFits outputFits
  | .fst left right fits code => do
      let pair ← code.compile allocation
      pure (pair.then (Implementation.first allocation left right hw fits))
  | .snd left right fits code => do
      let pair ← code.compile allocation
      pure (pair.then (Implementation.second allocation left right hw fits))
  | .nil input entry capacity countFits storageFits =>
      some (ListData.empty cost allocation input entry capacity hw countFits storageFits)
  | .cons entry capacity countFits storageFits headCode tailCode duplicateFits middleFits => do
      let head ← headCode.compile allocation
      let tail ← tailCode.compile allocation
      let frame ← head.checkedPair tail allocation hw duplicateFits middleFits (by
        change entry.representation.encoding.words + (1 + capacity * entry.representation.encoding.words) < 2 ^ w
        nlinarith)
      pure (frame.then (ListData.cons cost allocation entry capacity hw countFits storageFits))
  | .branch test left right duplicateFits tagFits => do
      let condition ← test.compile allocation
      let yes ← left.compile allocation
      let no ← right.compile allocation
      condition.checkedBranch (hw := hw) yes no allocation duplicateFits tagFits
  | .letE (input := input) _ duplicateFits frameFits binding code => do
      let value ← binding.compile allocation
      let body ← code.compile allocation
      let frame ← value.checkedPair (Implementation.identity input (width_pos hw)) allocation hw
        duplicateFits frameFits frameFits
      pure (frame.then body)
  | .op _ implementation code => do
      let argument ← code.compile allocation
      pure (argument.then implementation)
  | .fold input entry state capacity countFits argFits frameFits valueCode initialCode bodyCode => do
      let values ← valueCode.compile allocation
      let initial ← initialCode.compile allocation
      let body ← bodyCode.compile allocation
      let accumulator ← initial.checkedPair (Implementation.identity input (width_pos hw)) allocation hw
        (by omega) (by omega) (by omega)
      let frame ← values.checkedPair accumulator allocation hw (by omega)
        (by change (1 + capacity * entry.representation.encoding.words) + input.representation.encoding.words < 2 ^ w; omega)
        (by change (1 + capacity * entry.representation.encoding.words) + (state.representation.encoding.words + input.representation.encoding.words) < 2 ^ w; omega)
      if nameFits : body.program.savedBuffer < 2 ^ w then
        pure (frame.then (FoldImplementation.compile entry state input argFits body allocation hw nameFits capacity countFits frameFits))
      else none
  | .view code preserves sameBytes => do
      let body ← code.compile allocation
      pure (body.then (Implementation.view (width_pos hw) preserves sameBytes))
  | .listWiden entry source target increasing countFits storageFits code => do
      let body ← code.compile allocation
      pure (body.then (ListData.widen cost allocation entry source target increasing hw countFits storageFits))

/-- Successful compilation implements the original source result on every
represented input, for every tape and caller state satisfying its convention. -/
theorem Compilation.exec (allocation : 1 ≤ cost.allocPerWord) {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P cost hw expression input output)
    (implementation : Implementation cost input output (expression.denote P))
    (_compiled : certificate.compile allocation = some implementation)
    (tape : RandomTape w) (environment : Env base Γ) (valid : input.valid environment)
    (before : State w) (represented : input.representation.Holds ⟨environment, valid⟩ before) :
    ∃ after net peak, Caliper.Exec cost tape implementation.program.code before after
      (implementation.program.time ⟨environment, valid⟩) net peak ∧
      output.representation.Holds ⟨expression.denote P environment, implementation.preserves environment valid⟩ after ∧
      net ≤ implementation.program.net ⟨environment, valid⟩ ∧
      peak ≤ implementation.program.workspace ⟨environment, valid⟩ :=
  implementation.exec tape environment valid before represented

end Signatures.Runtime.CaliperBackend.SourceExpression
