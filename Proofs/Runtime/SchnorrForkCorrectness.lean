import Proofs.Runtime.SchnorrForkRefinement

/-! Relating the executable controller to the typed, indexed fork. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

noncomputable def extractValues
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
  if first.1.1.2.1 = second.1.1.2.1 ∧ first.1.2 ≠ second.1.2 then
    pure ((first.1.1.2.2 - second.1.1.2.2) / (first.1.2 - second.1.2))
  else $ᵗ F

noncomputable def checkSecond (cost : PrimitiveCosts) (qH : Nat)
    (i : Fin (qH + 1)) (old : F)
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
  match splitCells i second.2.2 with
  | none => $ᵗ F
  | some (_, fresh) =>
    if old = fresh then $ᵗ F
    else if asIndex qH (selectionRun cost second qH).value = some i then
      extractValues first second
    else $ᵗ F

theorem finishValue_checked (cost : PrimitiveCosts) (qH : Nat) (i : Fin (qH + 1))
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M))
    (scan₁ : scanResult.Value (cryptoBase F G₁ G₂ K M)) :
    finishValue first second (true, i.val) (selectionRun cost second qH).value scan₁
        (scanCode.run (arithmetic F G₁ G₂ K M cost) (i.val, second.2.2, ())).value =
      checkSecond cost qH i scan₁.2.1 first second := by
  let choice := (selectionRun cost second qH).value
  let scanned := (scanCode.run (arithmetic F G₁ G₂ K M cost) (i.val, second.2.2, ())).value
  have hs := scanCode_split (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost i.val second.2.2
  change (if scanned.1 then some (scanned.2.2.2, scanned.2.1) else none) = _ at hs
  have hg : forkAccepted first second (true, i.val) choice scan₁ scanned ↔
      scanned.1 = true ∧ scan₁.2.1 ≠ scanned.2.1 ∧ asIndex qH choice = some i ∧
        first.1.1.2.1 = second.1.1.2.1 ∧ first.1.2 ≠ second.1.2 := by
    rw [asIndex_eq_some_iff]
    constructor
    · rintro ⟨hc, hi, hs, ha, hR, hchallenge⟩
      exact ⟨hs, ha, ⟨hc, hi.symm⟩, hR, hchallenge⟩
    · rintro ⟨hs, ha, ⟨hc, hi⟩, hR, hchallenge⟩
      exact ⟨hc, hi.symm, hs, ha, hR, hchallenge⟩
  change (if forkAccepted first second (true, i.val) choice scan₁ scanned then _ else _) = _
  simp only [hg]
  unfold checkSecond
  rw [← hs]
  change (if _ then _ else _) =
    match (if scanned.1 then some (scanned.2.2.2, scanned.2.1) else none) with
    | none => _
    | some (_, fresh) => if scan₁.2.1 = fresh then _
      else if asIndex qH choice = some i then _ else _
  by_cases hscan : scanned.1 = true <;> by_cases ha : scan₁.2.1 = scanned.2.1 <;>
    by_cases hc : asIndex qH choice = some i <;>
    simp [hscan, ha, hc, extractValues]

noncomputable def firstChecked (cost : PrimitiveCosts) (qH : Nat)
    (pass : List (TapeCell F) → ProbComp (loggedOutput.Value (cryptoBase F G₁ G₂ K M)))
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
  match asIndex qH (selectionRun cost first qH).value with
  | none => $ᵗ F
  | some i =>
    match splitCells i first.2.2 with
    | none => $ᵗ F
    | some (prior, old) => pass prior >>= checkSecond cost qH i old first

theorem firstValue_checked (cost : PrimitiveCosts) (qH : Nat)
    (pass : List (TapeCell F) → ProbComp (loggedOutput.Value (cryptoBase F G₁ G₂ K M)))
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) :
    firstValue cost qH pass first = firstChecked cost qH pass first := by
  by_cases hc : (selectionRun cost first qH).value.1 = true
  · let i : Fin (qH + 1) := ⟨(selectionRun cost first qH).value.2, selectionRun_valid cost first qH hc⟩
    have hi : asIndex qH (selectionRun cost first qH).value = some i :=
      (asIndex_eq_some_iff qH _ i).mpr ⟨hc, rfl⟩
    have he : (selectionRun cost first qH).value = (true, i.val) := Prod.ext hc rfl
    unfold firstValue firstChecked
    rw [hi]
    simp only [he, ite_true]
    have hs := scanCode_split (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost i.val first.2.2
    rw [← hs]
    split
    · unfold secondValue
      congr 1
      funext second
      exact finishValue_checked cost qH i first second _
    · rfl
  · simp [firstValue, firstChecked, asIndex, hc]

abbrev cachePassOutput : Ty CryptoAtom := .pair observedForgery cacheStore

noncomputable def selectPass (cost : PrimitiveCosts) (qH : Nat)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) : Option (Fin (qH + 1)) :=
  asIndex qH (selectionRun cost (p.1, p.2, []) qH).value

omit [SampleableType F] in
theorem selectionRun_log (cost : PrimitiveCosts) (qH : Nat)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (log : List (TapeCell F)) :
    selectionRun cost (p.1, p.2, log) qH = selectionRun cost (p.1, p.2, []) qH := rfl

noncomputable def extractFork
    (forked : Option (cachePassOutput.Value (cryptoBase F G₁ G₂ K M) ×
      cachePassOutput.Value (cryptoBase F G₁ G₂ K M))) : ProbComp F :=
  match forked with
  | none => $ᵗ F
  | some (first, second) => extractValues (first.1, first.2, []) (second.1, second.2, [])

/-- The executable controller, after cost erasure, is the encoded typed fork followed
by the guarded extractor. This is an equality of distributions, not just supports. -/
theorem forkValue_indexed (cost : PrimitiveCosts) (qH : Nat)
    (main : OracleComp (replaySpec F) (cachePassOutput.Value (cryptoBase F G₁ G₂ K M))) :
    forkValue cost qH (fun tape => (fun p => (p.1.1, p.1.2, p.2)) <$>
      simulateQ sampleReplay (indexedLoggedRun main tape)) =
      (simulateQ sampleReplay (indexedFork main qH (selectPass cost qH)) >>= extractFork) := by
  unfold forkValue
  have hfirst (pass : List (TapeCell F) → ProbComp (loggedOutput.Value (cryptoBase F G₁ G₂ K M))) :
      firstValue cost qH pass = firstChecked cost qH pass := funext (firstValue_checked cost qH pass)
  rw [hfirst]
  unfold firstChecked indexedFork
  simp only [bind_map_left, simulateQ_bind, bind_assoc]
  congr 1
  funext first
  rw [selectionRun_log cost qH first.1 first.2]
  unfold selectPass
  cases hc : asIndex qH (selectionRun (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost (first.1.1, first.1.2, []) qH).value with
  | none => simp [simulateQ_pure, extractFork]
  | some i =>
    dsimp only
    cases hs : splitCells i first.2 with
    | none => simp [simulateQ_pure, extractFork]
    | some prior =>
      simp only [simulateQ_bind, bind_assoc]
      congr 1
      funext second
      unfold checkSecond
      rw [selectionRun_log cost qH second.1 second.2]
      cases ht : splitCells i second.2 with
      | none => simp [simulateQ_pure, extractFork]
      | some later =>
        by_cases ha : prior.2 = later.2 <;>
          by_cases hb : asIndex qH (selectionRun (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
            cost (second.1.1, second.1.2, []) qH).value = some i <;>
          simp [ha, hb, simulateQ_pure, extractFork, extractValues]

theorem forkCode_indexed (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> (forkCode randomBound source).run cost sampling (pk, g, qH, data, ()) =
      (simulateQ sampleReplay (indexedFork
        ((macroPass cost randomBound source (pk, data, ())).run ((g, pk), [], []))
        qH (selectPass cost qH)) >>= extractFork) := by
  rw [forkCode_value]
  exact forkValue_indexed cost qH _

noncomputable def sampleExpanded : QueryImpl (expandedSpec F) ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr () => $ᵗ F

omit [Field F] [DecidableEq F] in
theorem sampleExpanded_liftRandom {A : Type} (main : ProbComp A) :
    simulateQ (sampleExpanded (F := F)) (liftRandom main) = main := by
  induction main using OracleComp.inductionOn with
  | pure value => simp [liftRandom]
  | query_bind n next ih =>
    simpa only [liftRandom, simulateQ_bind, simulateQ_spec_query, sampleExpanded] using
      congrArg (fun f : Fin (n + 1) → ProbComp A => (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= f)
        (funext ih)

omit [Field F] [DecidableEq F] in
theorem sampleExpanded_expand {A : Type} (main : OracleComp (replaySpec F) A) :
    simulateQ sampleExpanded (simulateQ (Replay.expandPrivate privateImpl) main) =
      simulateQ sampleReplay main := by
  induction main using OracleComp.inductionOn with
  | pure value => simp
  | query_bind i next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    cases i with
    | inl i =>
      cases i with
      | inl n => simp only [Replay.expandPrivate, privateImpl,
          simulateQ_spec_query, sampleExpanded, sampleReplay, ih]
      | inr u =>
        cases u
        simp only [Replay.expandPrivate, privateImpl,
          sampleExpanded_liftRandom, sampleReplay, ih]
    | inr u =>
      cases u
      simp only [Replay.expandPrivate, simulateQ_spec_query,
        sampleExpanded, sampleReplay, ih]

/-- Private scalar samplers may use multiple uniform queries: after expansion the
same costed machine implements the upstream primitive-boundary contextual fork. -/
theorem forkCode_context (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> (forkCode randomBound source).run cost sampling (pk, g, qH, data, ()) =
      (simulateQ sampleExpanded (contextFork
        (simulateQ (Replay.expandPrivate privateImpl)
          ((macroPass cost randomBound source (pk, data, ())).run ((g, pk), [], [])))
        (fun _ => qH) (.inr ()) (selectPass cost qH)) >>= extractFork) := by
  rw [forkCode_indexed, ← expand_indexedFork, sampleExpanded_expand]

end Signatures.Runtime.Schnorr
