import Proofs.SynchronizedPS.LazyGame
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Synchronized PS as two weighted schemes with a known correction

With `y` known, `(x + y·m)•H(t)` is the weighted signature `x•H(t)` of the scheme with terms
`[(t, 1)]` plus the correction `(y·m)•H(t)`; with `x` known it is `y•(m•H(t))`, the scheme with
terms `[(t, m)]`, plus `x•H(t)`. A wrapper around the attacker hashes the period before each
signing query, adds the correction to the reply, and reports the weighted forgery
`σ* − final•H(t*)` with the coefficients re-expressed over its own hash replies: the attacker's
coefficients on its own hash queries, `ξ_j·correction(m_j)` on the pre-sign hashes, `−final` on a
last hash of the attacked period. The weighted solvers run on the wrapped attacker are then the
synchronized PS solvers. The two transcripts of `Reduction.run` forget the interleaving of hash
and signing replies that the wrapper's coefficient positions depend on, so this file first
records the attacker's run as an ordered event list. -/

open OracleComp OracleSpec Model Model.LazyAGM

namespace SynchronizedPS.Wrapped

variable {F Period G₁ G₂ : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- One reply the attacker received, in order: a hash of a period or a signature on a message. -/
inductive Event (F Period : Type)
  | hash (period : Period)
  | sign (message : Period × F)

/-- Fixed-table handler recording the attacker's queries in order. -/
def orderedImpl (H : Period → G₁) (sign : Period × F → G₁) :
    QueryImpl (advSpec Period (Period × F) G₁) (StateT (List (Event F Period)) ProbComp) := fun
  | .inl (.inl n) => StateT.mk fun events => do
      let u ← (unifSpec.query n : ProbComp (Fin (n + 1)))
      pure (u, events)
  | .inl (.inr t) => StateT.mk fun events => pure (H t, events ++ [Event.hash t])
  | .inr m => StateT.mk fun events => pure (sign m, events ++ [Event.sign m])

def orderedRun (V : Proofs.View F Period G₁ G₂) (publicKey : G₂ × G₂)
    (H : Period → G₁) (sign : Period × F → G₁) :
    ProbComp (Output F (Forgery F Period) × List (Event F Period)) :=
  (simulateQ (orderedImpl H sign) (V.main publicKey)).run []

/-- The two transcripts, read off the ordered events. -/
def hashes (H : Period → G₁) : List (Event F Period) → List (Period × G₁)
  | [] => []
  | .hash t :: rest => (t, H t) :: hashes H rest
  | .sign _ :: rest => hashes H rest

def signatures (sign : Period × F → G₁) : List (Event F Period) → List ((Period × F) × G₁)
  | [] => []
  | .hash _ :: rest => signatures sign rest
  | .sign m :: rest => (m, sign m) :: signatures sign rest

def transcript (H : Period → G₁) (sign : Period × F → G₁) (events : List (Event F Period)) :
    Transcript Period (Period × F) G₁ :=
  (hashes H events, signatures sign events)

omit [Field F] [AddCommGroup G₁] [Module F G₁] in
theorem hashes_append (H : Period → G₁) (events more : List (Event F Period)) :
    hashes H (events ++ more) = hashes H events ++ hashes H more := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [hashes, ih]

omit [Field F] [AddCommGroup G₁] [Module F G₁] in
theorem signatures_append (sign : Period × F → G₁) (events more : List (Event F Period)) :
    signatures sign (events ++ more) = signatures sign events ++ signatures sign more := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [signatures, ih]

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
/-- `Reduction.run` is the ordered run with the transcripts read off. -/
theorem run_eq_ordered (V : Proofs.View F Period G₁ G₂)
    (publicKey : G₂ × G₂) (H : Period → G₁) (sign : Period × F → G₁) :
    Proofs.runV V publicKey H sign =
      (fun z => (z.1, transcript H sign z.2)) <$> orderedRun V publicKey H sign := by
  unfold Proofs.runV orderedRun
  have h := map_run_simulateQ_eq_of_query_map_eq (orderedImpl H sign) (fixedImpl H sign)
    (transcript H sign) (by
      intro q events
      rcases q with (n | t) | m <;>
        simp [orderedImpl, fixedImpl, handler, transcript, StateT.run_mk, hashes_append,
          signatures_append, hashes, signatures, Functor.map_map, Prod.map])
    (V.main publicKey) []
  exact h.symm

/-! ## The wrapper -/

/-- Forward randomness and hashes, recording them; before a signing query hash its period, and
add `correction m • H(t)` to the signer's reply. -/
def translator (correction : Period × F → F) :
    QueryImpl (advSpec Period (Period × F) G₁)
      (StateT (List (Event F Period)) (OracleComp (advSpec Period (Period × F) G₁)))
  | .inl (.inl n) => StateT.mk fun events => do
      let u ← (liftM ((advSpec Period (Period × F) G₁).query (.inl (.inl n))) :
        OracleComp (advSpec Period (Period × F) G₁) (Fin (n + 1)))
      pure (u, events)
  | .inl (.inr t) => StateT.mk fun events => do
      let point ← (liftM ((advSpec Period (Period × F) G₁).query (.inl (.inr t))) :
        OracleComp (advSpec Period (Period × F) G₁) G₁)
      pure (point, events ++ [Event.hash t])
  | .inr m => StateT.mk fun events => do
      let point ← (liftM ((advSpec Period (Period × F) G₁).query (.inl (.inr m.1))) :
        OracleComp (advSpec Period (Period × F) G₁) G₁)
      let signature ← (liftM ((advSpec Period (Period × F) G₁).query (.inr m)) :
        OracleComp (advSpec Period (Period × F) G₁) G₁)
      pure (signature + correction m • point, events ++ [Event.sign m])

/-- The wrapper's hash coefficients: the attacker's on its own hashes (counted by `i`),
`ξ_j · correction(m_j)` on the hash before its `j`-th signing query. -/
def remap (correction : Period × F → F) (γ ξ : List F) :
    List (Event F Period) → Nat → Nat → List F
  | [], _, _ => []
  | .hash _ :: rest, i, j => tokenCoeff γ i :: remap correction γ ξ rest (i + 1) j
  | .sign m :: rest, i, j => tokenCoeff ξ j * correction m :: remap correction γ ξ rest i (j + 1)

/-- The attacker wrapped for a weighted scheme: `keys` builds its key pair from the weighted
public key and the known key, `final` is the scalar on `H(t*)` subtracted from the forgery. -/
def wrap (correction : Period × F → F) (final : Forgery F Period → F) (keys : G₂ → G₂ × G₂)
    (V : Proofs.View F Period G₁ G₂) :
    Model.LazyAGM.Adversary F Period (Period × F) G₁ G₂ where
  main publicKey := do
    let (out, events) ← (simulateQ (translator correction) (V.main (keys publicKey))).run []
    let _ ← (liftM ((advSpec Period (Period × F) G₁).query (.inl (.inr out.mstar.1.1))) :
      OracleComp (advSpec Period (Period × F) G₁) G₁)
    pure ⟨out.mstar.1, out.β, remap correction out.γ out.ξ events 0 0 ++ [-(final out.mstar)], out.ξ⟩

/-- The wrapper's hash replies: every event hashed, then the attacked period. -/
def wrappedHashes (H : Period → G₁) : List (Event F Period) → List (Period × G₁)
  | [] => []
  | .hash t :: rest => (t, H t) :: wrappedHashes H rest
  | .sign m :: rest => (m.1, H m.1) :: wrappedHashes H rest

omit [Field F] [AddCommGroup G₁] [Module F G₁] in
theorem wrappedHashes_append (H : Period → G₁) (events more : List (Event F Period)) :
    wrappedHashes H (events ++ more) = wrappedHashes H events ++ wrappedHashes H more := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [wrappedHashes, ih]

/-- The wrapped output and transcript, from the attacker's ordered run against the corrected
signer `signO m + correction m • H m.1`. -/
def wrapped (correction : Period × F → F) (final : Forgery F Period → F) (H : Period → G₁)
    (signO : Period × F → G₁) (z : Output F (Forgery F Period) × List (Event F Period)) :
    Output F (Period × F) × Transcript Period (Period × F) G₁ :=
  (⟨z.1.mstar.1, z.1.β, remap correction z.1.γ z.1.ξ z.2 0 0 ++ [-(final z.1.mstar)], z.1.ξ⟩,
    wrappedHashes H z.2 ++ [(z.1.mstar.1.1, H z.1.mstar.1.1)], signatures signO z.2)

private theorem translator_run {β : Type} (correction : Period × F → F) (H : Period → G₁)
    (signO : Period × F → G₁) (program : OracleComp (advSpec Period (Period × F) G₁) β)
    (events : List (Event F Period)) :
    (simulateQ (fixedImpl H signO) ((simulateQ (translator correction) program).run events)).run
        (wrappedHashes H events, signatures signO events) =
      (fun z => ((z.1, z.2), (wrappedHashes H z.2, signatures signO z.2))) <$>
        (simulateQ (orderedImpl H (fun m => signO m + correction m • H m.1)) program).run events := by
  induction program using OracleComp.inductionOn generalizing events with
  | pure value => simp [StateT.run_pure]
  | query_bind q next ih =>
      rcases q with (n | t) | m
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, translator, orderedImpl,
          StateT.run_mk, fixedImpl, handler, bind_assoc, pure_bind]
        exact bind_congr fun u => ih u events
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, translator, orderedImpl,
          StateT.run_mk, fixedImpl, handler, bind_assoc, pure_bind]
        have := ih (H t) (events ++ [Event.hash t])
        simpa only [wrappedHashes_append, signatures_append, wrappedHashes, signatures,
          List.append_nil, fixedImpl] using this
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, translator, orderedImpl,
          StateT.run_mk, fixedImpl, handler, bind_assoc, pure_bind]
        have := ih (signO m + correction m • H m.1) (events ++ [Event.sign m])
        simpa only [wrappedHashes_append, signatures_append, wrappedHashes, signatures,
          List.append_nil, fixedImpl] using this

omit [AddCommGroup G₂] [Module F G₂] in
/-- Running the wrapper against fixed tables is the attacker's ordered run against the corrected
signer, followed by `wrapped`. -/
theorem fixedRun_wrap (correction : Period × F → F) (final : Forgery F Period → F) (keys : G₂ → G₂ × G₂)
    (V : Proofs.View F Period G₁ G₂) (publicKey : G₂)
    (H : Period → G₁) (signO : Period × F → G₁) :
    fixedRun (wrap correction final keys V) publicKey H signO =
      wrapped correction final H signO <$>
        orderedRun V (keys publicKey) H (fun m => signO m + correction m • H m.1) := by
  unfold fixedRun orderedRun wrap
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_pure]
  have := translator_run correction H signO (V.main (keys publicKey)) []
  simp only [wrappedHashes, signatures] at this
  rw [this]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  rintro ⟨out, events⟩
  simp [fixedImpl, handler, StateT.run_mk, wrapped]

end SynchronizedPS.Wrapped
