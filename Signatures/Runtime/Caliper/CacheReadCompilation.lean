import Signatures.Runtime.Caliper.CacheReadFinish
import Signatures.Runtime.Caliper.CacheBounds
import Signatures.Runtime.Caliper.InteractiveControlBounds
import Signatures.Runtime.Caliper.InteractiveDescription

/-! Cache reads with an executed primitive draw only on misses. The miss frame
is saved outside the lowered draw's buffer footprint and restored by charged
instructions. The primitive provides its own source refinement; every other
part of the complete cache read is constructed here. -/

namespace Signatures.Runtime.CaliperBackend.CacheRead

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {K V I : Type} {spec : OracleSpec I}
    (layout : CacheLayout w K V) (port : Interactive.Port w spec)

def drawnValue (frame : (no layout).Value) (fresh : layout.value.Value) : (drawn layout).Value :=
  ⟨(fresh.val, frame.val), fresh.property, frame.property⟩

def completed (value : (drawn layout).Value) : (output layout).Value :=
  ⟨(value.val.1, (value.val.2.2.1, value.val.1) :: value.val.2.2.2.2.1),
    (finish layout).preserves value.val value.property⟩

def hitDenote (frame : (yes layout).Value) : OracleComp spec (output layout).Value :=
  pure ⟨(frame.val.1.2, frame.val.2.2.2.1), (hit layout).preserves frame.val frame.property⟩

def missDenote (drawSource : OracleComp spec layout.value.Value) (frame : (no layout).Value) :
    OracleComp spec (output layout).Value :=
  (fun fresh => completed layout (drawnValue layout frame fresh)) <$> drawSource

def drawCode (draw : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain draw (Interactive.savedBuffer port draw) layout.lookup.unit.representation.encoding.words
    layout.value.representation.encoding.words (no layout).representation.encoding.words

def missCode (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (drawCode layout port draw) (.compute (finish layout).program.code)

variable {layout port}
    {drawSource : OracleComp spec layout.value.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => drawSource) draw)

include drawCorrect in
theorem draw_refines : Interactive.Refines port .unit (no layout).representation (drawn layout).representation
    (fun frame => drawnValue layout frame <$> drawSource) (drawCode layout port draw) := by
  have retained := drawCorrect.retain (by decide) (no layout).representation layout.wordFits
    (by change 0 + (no layout).representation.encoding.words < 2 ^ w; simpa using (no layout).representation.fits)
    (drawnFits layout)
  have viewed := (retained.viewInput (no layout).representation
    (fun frame => (⟨(), trivial⟩, frame)) (fun _ => rfl)).viewOutput (drawn layout).representation
    (productView layout.value (no layout)).symm (by
      intro value
      exact congrArg (layout.value.representation.prod (no layout).representation (drawnFits layout)).encoding.encode
        ((productView layout.value (no layout)).apply_symm_apply value))
  convert viewed using 1
  · funext frame
    exact PFunctor.FreeM.comp_map (productView layout.value (no layout)).symm (fun fresh => (fresh, frame)) drawSource
  · rfl

include drawCorrect in
theorem miss_refines : Interactive.Refines port .unit (no layout).representation (output layout).representation
    (missDenote layout drawSource) (missCode layout port draw) := by
  convert (draw_refines drawCorrect).seq (Interactive.Refines.compute port .unit (finish layout).program) using 1
  · funext frame
    simp only [bind_pure_comp]
    exact PFunctor.FreeM.comp_map (completed layout) (drawnValue layout frame) drawSource
  · rfl

variable (layout)

def choice : Layout w (CacheLayout.Frame K V ⊕ CacheLayout.Frame K V) :=
  (yes layout).sum (no layout) (width_pos layout.wordFits) (by simpa using layout.frame_tagFits)

def branchDenote (drawSource : OracleComp spec layout.value.Value) (value : (choice layout).Value) :
    OracleComp spec (output layout).Value :=
  Sum.elim (hitDenote layout) (missDenote layout drawSource) (sumView (yes layout) (no layout) value)

def branchCode (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (.compute (hit layout).program.code) (missCode layout port draw)
    (yes layout).representation.encoding.words (no layout).representation.encoding.words

include drawCorrect in
theorem branch_refines : Interactive.Refines port .unit (choice layout).representation (output layout).representation
    (branchDenote layout drawSource) (branchCode layout port draw) :=
  (Interactive.Refines.dispatch (yes layout).representation (no layout).representation (output layout).representation
    (Interactive.Refines.compute port .unit (hit layout).program) (miss_refines drawCorrect) (width_pos layout.wordFits)
    (by simpa using layout.frame_tagFits)).viewInput
      (choice layout).representation (sumView (yes layout) (no layout)) (fun _ => rfl)

end Signatures.Runtime.CaliperBackend.CacheRead

namespace Signatures.Runtime.CaliperBackend.EncodedCacheRead

open Caliper BoundedSource SourceExpression OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : CacheLayout w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

def choose : Implementation .unit layout.input (CacheRead.choice layout)
    (fun value => GuardedBranch.select (fun frame : CacheLayout.Frame (key.Value base) (val.Value base) => frame.1.1)
      ((lookupExpr comparison).denote P value, value)) :=
  (EncodedCache.frame layout P comparison correct).then
    (GuardedBranch.selector (hw := layout.wordFits) (CacheFinish.test layout) (by decide) (CacheFinish.test_nameFits layout)
      layout.frame_duplicateFits layout.frame_tagFits)

def chosen (value : layout.input.Value) : (CacheRead.choice layout).Value :=
  ⟨GuardedBranch.select (fun frame : CacheLayout.Frame (key.Value base) (val.Value base) => frame.1.1)
      ((lookupExpr comparison).denote P value.val, value.val),
    (choose layout P comparison correct).preserves value.val value.property⟩

variable {I : Type} {spec : OracleSpec I}

def denote (drawSource : OracleComp spec layout.value.Value) (value : layout.input.Value) :
    OracleComp spec (CacheRead.output layout).Value :=
  CacheRead.branchDenote layout drawSource (chosen layout P comparison correct value)

def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (choose layout P comparison correct).program.code) (CacheRead.branchCode layout port draw)

theorem refines (port : Interactive.Port w spec) (drawSource : OracleComp spec layout.value.Value)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => drawSource) draw) :
    Interactive.Refines port .unit layout.input.representation (CacheRead.output layout).representation
      (denote layout P comparison correct drawSource) (code layout P comparison correct port draw) := by
  convert (Interactive.Refines.compute port .unit (choose layout P comparison correct).program).seq
    (CacheRead.branch_refines layout drawCorrect) using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

theorem denote_value (drawSource : OracleComp spec layout.value.Value) (value : layout.input.Value) :
    Subtype.val <$> denote layout P comparison correct drawSource value =
      if ((lookupExpr comparison).denote P value.val).1 = true then
        pure (((lookupExpr comparison).denote P value.val).2, value.val.2.2.1)
      else (fun fresh => (fresh.val, (value.val.1, fresh.val) :: value.val.2.2.1)) <$> drawSource := by
  by_cases found : ((lookupExpr comparison).denote P value.val).1 = true <;>
    simp [denote, chosen, GuardedBranch.select, CacheRead.branchDenote, sumView, found,
      CacheRead.hitDenote, CacheRead.missDenote, CacheRead.completed, CacheRead.drawnValue, Functor.map_map]

theorem source_eq {Cmd : Ty Atom → Ty Atom → Type} (H : SemanticsM base Cmd (OracleComp spec))
    (command : Cmd .unit val) (drawSource : OracleComp spec layout.value.Value)
    (drawErases : Subtype.val <$> drawSource = H command ()) (value : layout.input.Value) :
    Subtype.val <$> denote layout P comparison correct drawSource value =
      (cacheGetExpr comparison command).denote P H value.val := by
  rw [denote_value, cacheGetExpr_denote P H comparison command correct]
  have lookupEq : (lookupExpr comparison).denote P value.val = lookupValue value.val.1 value.val.2.1 value.val.2.2.1 := by
    simpa only [Expr.run_value] using lookupExpr_value P comparison correct value.val.1 value.val.2.1 value.val.2.2.1
  rw [lookupEq]
  split_ifs
  · rfl
  · rw [← drawErases, Functor.map_map]

/-- Decoding the executed program recovers the original effectful source
expression, including its oracle-call tree and all returned cache entries. -/
theorem observe {Cmd : Ty Atom → Ty Atom → Type} (H : SemanticsM base Cmd (OracleComp spec))
    (command : Cmd .unit val) (port : Interactive.Port w spec) (drawSource : OracleComp spec layout.value.Value)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => drawSource) draw) (drawErases : Subtype.val <$> drawSource = H command ())
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe (CacheRead.output layout).representation result) <$>
      (code layout P comparison correct port draw).execute port .unit tape before =
        some <$> (cacheGetExpr comparison command).denote P H value.val := by
  have observed := (refines layout P comparison correct port drawSource draw drawCorrect).observe tape value before holds
  have mapped := congrArg (fun computation : OracleComp spec (Option (CacheRead.output layout).Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  have erased := congrArg (fun computation : OracleComp spec (val.Value base × List (key.Value base × val.Value base)) => some <$> computation)
    (source_eq layout P comparison correct H command drawSource drawErases value)
  have middle : (fun result => Subtype.val <$> result) <$> some <$> denote layout P comparison correct drawSource value =
      some <$> Subtype.val <$> denote layout P comparison correct drawSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans
      (PFunctor.FreeM.comp_map (some : (val.Value base × List (key.Value base × val.Value base)) → Option _)
        (Subtype.val : (CacheRead.output layout).Value → _) (denote layout P comparison correct drawSource value))
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans (middle.trans erased))

end Signatures.Runtime.CaliperBackend.EncodedCacheRead
