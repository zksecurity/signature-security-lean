import Signatures.Runtime.Caliper.SchnorrROMReplayForkChoice

/-! The complete conditional fork controller. Rejected first selections skip
the fresh draw; repeated challenges skip replay; failed second selections
return failure. Admission to replay is derived from the first execution. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] [DecidableEq F]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

def secondCode (fuel : Nat) : Interactive.Code w :=
  .seq (ReplaySecond.Selected.program config caller ops qH indexFits fuel) (.compute (finish config).code)
def secondSource (fuel : Nat) (value : ReplaySecond.Request config) : ProbComp (Result config) :=
  if room : ReplaySecond.ready config fuel value then
    finishSource config <$> ReplaySecond.Selected.source config caller ops qH fuel ⟨value, room⟩
  else pure (.inl ())

omit [DecidableEq F] in
theorem second_refines (fuel : Nat) : Interactive.RefinesOn (ReplaySecond.ready config fuel)
    (Fresh.port config.handler.sampler.tape) .unit (ReplaySecond.rawInput config) (output config)
    (secondSource config caller ops qH fuel) (secondCode config caller ops qH indexFits fuel) := by
  have composed := (ReplaySecond.Selected.refines config caller ops qH indexFits fuel).seq
    (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (finish config))
  intro tape value room before holds
  have sourceEq : secondSource config caller ops qH fuel value =
      (ReplaySecond.Selected.source config caller ops qH fuel ⟨value, room⟩ >>= fun answer => pure (finishSource config answer)) := by
    unfold secondSource
    rw [dite_eq_left room]
    exact (bind_pure_comp (finishSource config) _).symm
  change Synchronizes _ (secondSource config caller ops qH fuel value) _
  rw [sourceEq]
  exact composed tape ⟨value, room⟩ before holds

def guardCode (fuel : Nat) : Interactive.Code w :=
  Interactive.dispatch (secondCode config caller ops qH indexFits fuel)
    (.compute (reject config (ReplaySecond.rawInput config)).code)
      (ReplaySecond.rawInput config).encoding.words (ReplaySecond.rawInput config).encoding.words
def guardSource (fuel : Nat) : ReplaySecond.Request config ⊕ ReplaySecond.Request config → ProbComp (Result config) :=
  Sum.elim (secondSource config caller ops qH fuel) (fun _ => pure (.inl ()))

omit [DecidableEq F] in
theorem guard_refines (fuel : Nat) : Interactive.RefinesOn
    (Sum.elim (ReplaySecond.ready config fuel) (ReplaySecond.ready config fuel))
    (Fresh.port config.handler.sampler.tape) .unit (guardChoice config) (output config)
    (guardSource config caller ops qH fuel) (guardCode config caller ops qH indexFits fuel) :=
  Interactive.RefinesOn.dispatch _ _ _ (second_refines config caller ops qH indexFits fuel)
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
      (reject config (ReplaySecond.rawInput config))).on (ReplaySecond.ready config fuel))
        (width_pos config.sampler.wordFits) (guardChoice config).fits

def afterCode (fuel : Nat) : Interactive.Code w :=
  .seq (ReplayChallenge.Checked.program config) (guardCode config caller ops qH indexFits fuel)
def afterSource (fuel : Nat) (value : ReplayChallenge.Input config) : ProbComp (Result config) :=
  guardChoiceSource config value >>= guardSource config caller ops qH fuel

theorem after_refines (fuel : Nat) : Interactive.RefinesOn (savedReady config fuel)
    (Fresh.port config.handler.sampler.tape) .unit (ReplayChallenge.input config) (output config)
    (afterSource config caller ops qH fuel) (afterCode config caller ops qH indexFits fuel) :=
  ((guardChoice_refines config).on (savedReady config fuel)).seq (guard_refines config caller ops qH indexFits fuel)
    (guardChoice_ready config fuel)

def branchCode (fuel : Nat) : Interactive.Code w :=
  Interactive.dispatch (.compute (reject config (ReplayChallenge.input config)).code) (afterCode config caller ops qH indexFits fuel)
    (ReplayChallenge.input config).encoding.words (ReplayChallenge.input config).encoding.words
def branchSource (fuel : Nat) : ReplayChallenge.Input config ⊕ ReplayChallenge.Input config → ProbComp (Result config) :=
  Sum.elim (fun _ => pure (.inl ())) (afterSource config caller ops qH fuel)

theorem branch_refines (fuel : Nat) : Interactive.RefinesOn (Sum.elim (savedReady config fuel) (savedReady config fuel))
    (Fresh.port config.handler.sampler.tape) .unit (ReplayFirst.choice config) (output config)
    (branchSource config caller ops qH fuel) (branchCode config caller ops qH indexFits fuel) :=
  Interactive.RefinesOn.dispatch _ _ _
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
      (reject config (ReplayChallenge.input config))).on (savedReady config fuel))
    (after_refines config caller ops qH indexFits fuel) (width_pos config.sampler.wordFits) (ReplayFirst.choice config).fits

def program (fuel : Nat) : Interactive.Code w :=
  .seq (ReplayFirst.program config caller ops qH indexFits fuel) (branchCode config caller ops qH indexFits fuel)
def source (fuel : Nat) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value}) : ProbComp (Result config) :=
  ReplayFirst.choiceSource config caller ops qH indexFits fuel value >>= branchSource config caller ops qH fuel

omit [DecidableEq F] in
theorem first_ready (fuel : Nat) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value})
    (answer) (reached : answer ∈ support (ReplayFirst.choiceSource config caller ops qH indexFits fuel value)) :
    Sum.elim (savedReady config fuel) (savedReady config fuel) answer := by
  have ready := ReplayFirst.choice_ready config caller ops qH indexFits fuel value answer reached ⟨0, trivial⟩
  cases answer <;> exact ready

theorem refines (fuel : Nat) : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (ReplayFirst.input config fuel) (output config) (source config caller ops qH indexFits fuel) (program config caller ops qH indexFits fuel) := by
  have joined := ((ReplayFirst.choice_refines config caller ops qH indexFits fuel).on (fun _ => True)).seq
    (branch_refines config caller ops qH indexFits fuel)
      (fun value _ => first_ready config caller ops qH indexFits fuel value)
  intro tape value before holds
  exact joined tape value trivial before holds

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
