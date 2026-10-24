import Proofs.Runtime.Caliper.SchnorrROMReplayFork

/-! Complete time and stored-code bounds for the conditional fork. Both stored
alternatives are counted; only the selected alternative contributes runtime. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] [DecidableEq F]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w) (budget : Handler.Budget config ops)
    (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

def secondTime (fuel : Nat) := ReplaySecond.Selected.timeBudget config caller ops qH indexFits budget localBudget fuel + finishTime config
def secondWords (fuel : Nat) := ReplaySecond.Selected.codeBudget config caller ops qH indexFits budget localBudget fuel + finishWords config + 2
omit [DecidableEq F] in
theorem second_time (fuel : Nat) : Interactive.TimeBoundOn (ReplaySecond.ready config fuel) (Fresh.port config.handler.sampler.tape) .unit
    (ReplaySecond.rawInput config) (secondCode config caller ops qH indexFits fuel) (secondTime config caller ops qH indexFits budget localBudget fuel) := by
  have composed := Interactive.TimeBound.seq (ReplaySecond.Selected.refines config caller ops qH indexFits fuel)
    (ReplaySecond.Selected.time config caller ops qH indexFits budget localBudget fuel)
    (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit) (finish config) _ (finish_time config))
  intro tape value room before holds
  exact composed tape ⟨value, room⟩ before holds
omit [DecidableEq F] in
theorem second_words (fuel : Nat) : ((secondCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    secondWords config caller ops qH indexFits budget localBudget fuel := by
  have replayed := ReplaySecond.Selected.words config caller ops qH indexFits budget localBudget fuel
  have finished := finish_words config
  change (WordIO.Code.seq ((ReplaySecond.Selected.program config caller ops qH indexFits fuel).lower _) (.compute (finish config).code)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold secondWords
  omega

def guardTime (fuel : Nat) := Interactive.dispatchTime (w := w) .unit
  (ReplaySecond.rawInput config).encoding.words (ReplaySecond.rawInput config).encoding.words
  (secondTime config caller ops qH indexFits budget localBudget fuel) (8 * (output config).encoding.words)
def guardWords (fuel : Nat) := secondWords config caller ops qH indexFits budget localBudget fuel +
  26 * (output config).encoding.words + 52 * (ReplaySecond.rawInput config).encoding.words + 55

omit [DecidableEq F] in
theorem guard_time (fuel : Nat) : Interactive.TimeBoundOn
    (Sum.elim (ReplaySecond.ready config fuel) (ReplaySecond.ready config fuel))
    (Fresh.port config.handler.sampler.tape) .unit (guardChoice config) (guardCode config caller ops qH indexFits fuel)
    (guardTime config caller ops qH indexFits budget localBudget fuel) :=
  Interactive.TimeBoundOn.dispatch _ _ (second_time config caller ops qH indexFits budget localBudget fuel)
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (reject config (ReplaySecond.rawInput config)) _ (reject_time config _)).on (ReplaySecond.ready config fuel))
    (width_pos config.sampler.wordFits) (guardChoice config).fits

omit [DecidableEq F] in
theorem guard_words (fuel : Nat) : ((guardCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    guardWords config caller ops qH indexFits budget localBudget fuel := by
  have replayed := second_words config caller ops qH indexFits budget localBudget fuel
  have rejected := reject_words config (ReplaySecond.rawInput config)
  change ((Interactive.dispatch (secondCode config caller ops qH indexFits fuel) (.compute (reject config (ReplaySecond.rawInput config)).code) _ _).lower _).descriptionWords ≤ _
  rw [Interactive.dispatch_descriptionWords]
  change ((secondCode config caller ops qH indexFits fuel).lower _).descriptionWords +
    (descriptionWords (reject config (ReplaySecond.rawInput config)).code + 1) +
      26 * (ReplaySecond.rawInput config).encoding.words + 26 * (ReplaySecond.rawInput config).encoding.words + 40 ≤ _
  unfold guardWords
  omega

def afterTime (fuel : Nat) := ReplayChallenge.Checked.timeBudget config + guardTime config caller ops qH indexFits budget localBudget fuel
def afterWords (fuel : Nat) := ReplayChallenge.Checked.codeBudget config + guardWords config caller ops qH indexFits budget localBudget fuel + 1

theorem after_time (fuel : Nat) : Interactive.TimeBoundOn (savedReady config fuel) (Fresh.port config.handler.sampler.tape) .unit
    (ReplayChallenge.input config) (afterCode config caller ops qH indexFits fuel) (afterTime config caller ops qH indexFits budget localBudget fuel) :=
  Interactive.TimeBoundOn.seq ((guardChoice_refines config).on (savedReady config fuel))
    ((ReplayChallenge.Checked.time config).on (savedReady config fuel)) (guard_time config caller ops qH indexFits budget localBudget fuel)
    (guardChoice_ready config fuel)
theorem after_words (fuel : Nat) : ((afterCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    afterWords config caller ops qH indexFits budget localBudget fuel := by
  have drawn := ReplayChallenge.Checked.words config
  have guarded := guard_words config caller ops qH indexFits budget localBudget fuel
  change (WordIO.Code.seq ((ReplayChallenge.Checked.program config).lower _) ((guardCode config caller ops qH indexFits fuel).lower _)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq]
  unfold afterWords
  omega

def branchTime (fuel : Nat) := Interactive.dispatchTime (w := w) .unit
  (ReplayChallenge.input config).encoding.words (ReplayChallenge.input config).encoding.words (8 * (output config).encoding.words)
  (afterTime config caller ops qH indexFits budget localBudget fuel)
def branchWords (fuel : Nat) := afterWords config caller ops qH indexFits budget localBudget fuel +
  26 * (output config).encoding.words + 52 * (ReplayChallenge.input config).encoding.words + 55

theorem branch_time (fuel : Nat) : Interactive.TimeBoundOn (Sum.elim (savedReady config fuel) (savedReady config fuel))
    (Fresh.port config.handler.sampler.tape) .unit (ReplayFirst.choice config) (branchCode config caller ops qH indexFits fuel)
    (branchTime config caller ops qH indexFits budget localBudget fuel) :=
  Interactive.TimeBoundOn.dispatch _ _
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (reject config (ReplayChallenge.input config)) _ (reject_time config _)).on (savedReady config fuel))
    (after_time config caller ops qH indexFits budget localBudget fuel) (width_pos config.sampler.wordFits) (ReplayFirst.choice config).fits

theorem branch_words (fuel : Nat) : ((branchCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    branchWords config caller ops qH indexFits budget localBudget fuel := by
  have continued := after_words config caller ops qH indexFits budget localBudget fuel
  have rejected := reject_words config (ReplayChallenge.input config)
  change ((Interactive.dispatch (.compute (reject config (ReplayChallenge.input config)).code) (afterCode config caller ops qH indexFits fuel) _ _).lower _).descriptionWords ≤ _
  rw [Interactive.dispatch_descriptionWords]
  change (descriptionWords (reject config (ReplayChallenge.input config)).code + 1) +
    ((afterCode config caller ops qH indexFits fuel).lower _).descriptionWords +
      26 * (ReplayChallenge.input config).encoding.words + 26 * (ReplayChallenge.input config).encoding.words + 40 ≤ _
  unfold branchWords
  omega

def timeBudget (fuel : Nat) := ReplayFirst.timeBudget config caller ops qH indexFits budget localBudget fuel +
  branchTime config caller ops qH indexFits budget localBudget fuel
def codeBudget (fuel : Nat) := ReplayFirst.codeBudget config caller ops qH indexFits budget localBudget fuel +
  branchWords config caller ops qH indexFits budget localBudget fuel + 1

theorem time (fuel : Nat) : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (ReplayFirst.input config fuel) (program config caller ops qH indexFits fuel) (timeBudget config caller ops qH indexFits budget localBudget fuel) := by
  have composed := Interactive.TimeBoundOn.seq
    ((ReplayFirst.choice_refines config caller ops qH indexFits fuel).on (fun _ => True))
    ((ReplayFirst.time config caller ops qH indexFits budget localBudget fuel).on (fun _ => True))
    (branch_time config caller ops qH indexFits budget localBudget fuel)
    (fun value _ => first_ready config caller ops qH indexFits fuel value)
  intro tape value before holds
  exact composed tape value trivial before holds

theorem words (fuel : Nat) : ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config caller ops qH indexFits budget localBudget fuel := by
  have first := ReplayFirst.words config caller ops qH indexFits budget localBudget fuel
  have branches := branch_words config caller ops qH indexFits budget localBudget fuel
  change (WordIO.Code.seq ((ReplayFirst.program config caller ops qH indexFits fuel).lower _) ((branchCode config caller ops qH indexFits fuel).lower _)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq]
  unfold codeBudget
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
