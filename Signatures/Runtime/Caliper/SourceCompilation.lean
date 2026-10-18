import Signatures.Runtime.Caliper.InteractiveRetain
import Signatures.Runtime.Caliper.Counted

/-! A bounded compilation certificate indexed by the existing reduction language.
Local leaves require actual Caliper implementations and capacity preservation.
Control is compiled structurally; no implementation of a completed reduction is
assumed. Mathematical source types and source games remain unchanged.

The constructors cover the whole source syntax, including input-counted
iteration. Its chosen input layout stores the payload followed by the counter;
primitive producers must implement that encoding like every other layout.
-/

namespace Signatures.Runtime.CaliperBackend.SourceCompilation

open Caliper OracleComp OracleSpec PFunctor BoundedSource

universe v u

variable {w : Nat} {I : Type} {spec : OracleSpec I}

structure Interface (w : Nat) (spec : OracleSpec I) where
  request : Layout w I
  reply : Representation w (Σ position : request.Value, spec.Range position.val)

def Interface.replyView (iface : Interface w spec) :
    {value : Σ position, spec.Range position // iface.request.valid value.1} ≃
      (Σ position : iface.request.Value, spec.Range position.val) where
  toFun value := ⟨⟨value.val.1, value.property⟩, value.val.2⟩
  invFun value := ⟨⟨value.1.val, value.2⟩, value.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Interface.response (iface : Interface w spec) : Layout w (Σ position, spec.Range position) where
  valid value := iface.request.valid value.1
  representation := iface.reply.transport iface.replyView

def Interface.port (iface : Interface w spec) : Interactive.Port w spec where
  Request := iface.request.Value
  source := Subtype.val
  request := iface.request.representation
  reply := iface.reply

def iterationView {A : Type} (state : Layout w A) (fuel : Nat) :
    {value : Nat × A // value.1 < fuel + 1 ∧ state.valid value.2} ≃ (state.Value × Fin (fuel + 1)) where
  toFun value := (⟨value.val.2, value.property.2⟩, ⟨value.val.1, value.property.1⟩)
  invFun value := ⟨(value.2.val, value.1.val), value.2.isLt, value.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A representation choice for the original `(Nat, state)` source input. This
does not convert an existing product's bytes without executing a conversion. -/
def iterationInput {A : Type} (state : Layout w A) (fuel : Nat) (hw : 16 < 2 ^ w)
    (counterFits : fuel + 1 ≤ 2 ^ w) (storageFits : state.representation.encoding.words + 1 < 2 ^ w) :
    Layout w (Nat × A) where
  valid value := value.1 < fuel + 1 ∧ state.valid value.2
  representation := (Interactive.Counted.frame state.representation fuel hw counterFits storageFits).transport (iterationView state fuel)

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
    {Q : QuantitativeStepClass.{0, v, u} C} {sourceIface : BackendProgram.Interface (C := C) spec}
    (targetIface : Interface w spec) (cost : WordIO.Costs) (hw : 16 < 2 ^ w)

inductive Compilation : {A B : Type} → {a : C.Str A} → {b : C.Str B} →
    BackendProgram.Code Q spec sourceIface a b → Layout w A → Layout w B → Type (max 1 v u) where
  | atomic {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
      {input : Layout w A} {output : Layout w B} (source : Q.Realizer a b f)
      (implementation : Implementation cost.machine input output f) :
      Compilation (.atomic source) input output
  | query : Compilation .query targetIface.request targetIface.response
  | seq {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
      {first : BackendProgram.Code Q spec sourceIface a b} {second : BackendProgram.Code Q spec sourceIface b d}
      {input : Layout w A} {middle : Layout w B} {output : Layout w D}
      (left : Compilation first input middle) (right : Compilation second middle output) :
      Compilation (.seq first second) input output
  | branch {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
      {left : BackendProgram.Code Q spec sourceIface a d} {right : BackendProgram.Code Q spec sourceIface b d}
      {leftInput : Layout w A} {rightInput : Layout w B} {output : Layout w D}
      (leftCode : Compilation left leftInput output) (rightCode : Compilation right rightInput output)
      (fits : 1 + max leftInput.representation.encoding.words rightInput.representation.encoding.words < 2 ^ w) :
      Compilation (.branch left right) (leftInput.sum rightInput (width_pos hw) fits) output
  | first {A B S : Type} {a : C.Str A} {b : C.Str B} (s : C.Str S)
      {body : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
      (saved : Layout w S) (code : Compilation body input output)
      (inputFits : input.representation.encoding.words + saved.representation.encoding.words < 2 ^ w)
      (outputFits : output.representation.encoding.words + saved.representation.encoding.words < 2 ^ w) :
      Compilation (.first s body) (input.prod saved inputFits) (output.prod saved outputFits)
  | loop {S B : Type} {s : C.Str S} {b : C.Str B}
      {body : BackendProgram.Code Q spec sourceIface s (StepClass.HasSum.sum b s)}
      {stop : BackendProgram.Code Q spec sourceIface s b}
      {state : Layout w S} {result : Layout w B}
      (fits : 1 + max result.representation.encoding.words state.representation.encoding.words < 2 ^ w)
      (step : Compilation body state (result.sum state (width_pos hw) fits))
      (finish : Compilation stop state result) (fuel : Nat) :
      Compilation (.loop body stop fuel) state result
  | iterate {S : Type} {s : C.Str S} (counter : C.Str Nat)
      {body : BackendProgram.Code Q spec sourceIface s s} {state : Layout w S}
      (code : Compilation body state state) (fuel : Nat)
      (counterFits : fuel + 1 ≤ 2 ^ w) (storageFits : state.representation.encoding.words + 1 < 2 ^ w) :
      Compilation (.iterate counter body) (iterationInput state fuel hw counterFits storageFits) state

variable {targetIface cost hw}

def Compilation.compile {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B} :
    Compilation targetIface cost hw source input output → Interactive.Code w
  | .atomic _ implementation => .compute implementation.program.code
  | .query => .query
  | .seq initial following => .seq initial.compile following.compile
  | .branch (leftInput := left) (rightInput := right) initial following _ =>
      Interactive.dispatch initial.compile following.compile left.representation.encoding.words right.representation.encoding.words
  | .first (input := input) (output := output) _ saved body _ _ =>
      Interactive.retain body.compile (Interactive.savedBuffer targetIface.port body.compile)
        input.representation.encoding.words output.representation.encoding.words saved.representation.encoding.words
  | .loop (state := state) (result := result) _ body stop fuel =>
      Interactive.loop body.compile stop.compile result.representation.encoding.words state.representation.encoding.words fuel
  | .iterate (state := state) _ body fuel _ _ =>
      Interactive.Counted.code body.compile (Interactive.savedBuffer targetIface.port body.compile) state.representation.encoding.words fuel

/-- This bounded denotation carries capacity witnesses only in the mathematical
specification. The compiler erases witnesses; no such data or callbacks execute. -/
def Compilation.boundedDenote {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B} :
    Compilation targetIface cost hw source input output → input.Value → OracleComp spec output.Value
  | .atomic _ implementation, value => pure ⟨_, implementation.preserves value.val value.property⟩
  | .query, value => queryBind value.val (fun answer => pure ⟨⟨value.val, answer⟩, value.property⟩)
  | .seq initial following, value => initial.boundedDenote value >>= following.boundedDenote
  | .branch (leftInput := left) (rightInput := right) initial following _, value =>
      Sum.elim initial.boundedDenote following.boundedDenote (sumView left right value)
  | .first (input := input) (output := output) _ saved body _ _, value =>
      (fun result => (productView output saved).symm (result, (productView input saved value).2)) <$>
        body.boundedDenote (productView input saved value).1
  | .loop (state := state) (result := result) _ body stop fuel, value =>
      BackendProgram.loopDenote (fun state => sumView result _ <$> body.boundedDenote state)
        stop.boundedDenote fuel value
  | .iterate _ body _ _ _, value => repeatDenote body.boundedDenote value.val.1 ⟨value.val.2, value.property.2⟩

theorem Compilation.correct {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) (allocation : 1 ≤ cost.machine.allocPerWord) :
    Interactive.Refines targetIface.port cost input.representation output.representation code.boundedDenote code.compile := by
  induction code with
  | atomic source implementation => exact Interactive.Refines.compute _ _ implementation.program
  | query =>
    have reference := Interactive.Refines.query targetIface.port cost
    have transported := reference.viewOutput targetIface.response.representation targetIface.replyView.symm (by
      intro value
      exact congrArg targetIface.reply.encoding.encode (targetIface.replyView.apply_symm_apply value))
    convert transported using 1 <;> rfl
  | seq first second ih₁ ih₂ => exact ih₁.seq ih₂
  | @branch A B D a b d left right leftInput rightInput output first second fits ih₁ ih₂ =>
    exact (Interactive.Refines.dispatch leftInput.representation rightInput.representation output.representation
      ih₁ ih₂ (width_pos hw) fits).viewInput
        (leftInput.sum rightInput (width_pos hw) fits).representation (sumView leftInput rightInput) (fun _ => rfl)
  | @first A B S a b s body input output saved code inputFits outputFits ih =>
    have retained := ih.retain allocation saved.representation hw inputFits outputFits
    have viewed := (retained.viewInput (input.prod saved inputFits).representation (productView input saved) (fun _ => rfl)).viewOutput
      (output.prod saved outputFits).representation (productView output saved).symm (by
        intro value
        exact congrArg (output.representation.prod saved.representation outputFits).encoding.encode
          ((productView output saved).apply_symm_apply value))
    convert viewed using 1
    · funext value
      exact PFunctor.FreeM.comp_map _ _ _
    · rfl
  | @loop S B s b body stop state result fits step finish fuel ihBody ihStop =>
    have viewed := ihBody.viewOutput (result.representation.sum state.representation (width_pos hw) fits)
      (sumView result state) (fun _ => rfl)
    exact Interactive.Refines.loop state.representation result.representation (width_pos hw) fits viewed ihStop fuel
  | @iterate S s counter body state code fuel counterFits storageFits ih =>
    exact (Interactive.Counted.refines state.representation ih allocation hw storageFits fuel counterFits).viewInput
      (iterationInput state fuel hw counterFits storageFits).representation (iterationView state fuel) (fun _ => rfl)

end Signatures.Runtime.CaliperBackend.SourceCompilation
