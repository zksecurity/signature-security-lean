import Signatures.Runtime.Coron
import Signatures.Runtime.CacheRefinement
import Signatures.Runtime.GrowingState

/-! Implemented lazy Coron replies. Field/group arithmetic and cache traversal execute the
first-order runtime language. Fixed adapter frames below charge packing/unpacking and state
plumbing; neither a map-valued cache lookup nor a whole-simulator opcode is executed.
The primitive sampling contract is arithmetic-machine cost, not a bit-level rejection bound. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Coron

structure SamplingCosts where
  scalar : Nat
  coin : Nat
  random : Nat

inductive Draw (qS : Nat) : Ty CryptoAtom → Ty CryptoAtom → Type
  | scalar : Draw qS .unit scalar
  | coin : Draw qS .unit (boundedNat qS)

/-- The arity of each private-random request is bounded in the source interface. -/
inductive Command (randomBound : Nat) : Ty CryptoAtom → Ty CryptoAtom → Type
  | random (n : Fin (randomBound + 1)) : Command randomBound .unit (boundedNat n.val)
  | hash : Command randomBound message point₁
  | sign : Command randomBound message point₁

def kind {r : Nat} {a b} : Command r a b → Fin 3
  | .random _ => 0
  | .hash => 1
  | .sign => 2

structure CacheState (F M : Type) (qS : Nat) where
  scalars : List (M × F)
  coins : List (M × Fin (qS + 1))
  signed : List M

def CacheState.empty {F M qS} : CacheState F M qS := ⟨[], [], []⟩

def CacheState.size {F M qS} (s : CacheState F M qS) : Nat :=
  max s.scalars.length (max s.coins.length s.signed.length)

def coinValue (qS : Nat) : Expr CryptoOp [boundedNat qS] .nat :=
  .op (.finVal qS) (.var .here)

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

omit [SampleableType F] in
theorem coinValue_run (cost : PrimitiveCosts) (qS : Nat) (k : Fin (qS + 1)) :
    (coinValue qS).run (arithmetic F G₁ G₂ M M cost) (k, ()) = ⟨k.val, cost.natOp + 2⟩ := by
  simp [coinValue, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, Nat.add_comm]
  omega

noncomputable def draws (qS : Nat) (cost : SamplingCosts) :
    Handler (cryptoBase F G₁ G₂ M M) (Draw qS) unifSpec := fun cmd _ => match cmd with
  | .scalar => (fun x => ⟨x, cost.scalar⟩) <$> ($ᵗ F : ProbComp F)
  | .coin => (fun x => ⟨x, cost.coin⟩) <$> (liftM (unifSpec.query qS) : ProbComp (Fin (qS + 1)))

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M] in
omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] in
private theorem draws_steps (qS : Nat) (cost : SamplingCosts) {a b} (cmd : Draw qS a b)
    (arg : a.Value (cryptoBase F G₁ G₂ M M))
    (z : Run (b.Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support (draws (F := F) (G₁ := G₁) (G₂ := G₂) (M := M) qS cost cmd arg)) :
    z.steps = match cmd with | .scalar => cost.scalar | .coin => cost.coin := by
  cases cmd <;> simp only [draws, support_map, Set.mem_image] at hz <;>
    obtain ⟨x, _, rfl⟩ := hz <;> rfl

/-- A fixed 24-step adapter frame charges the two binds, state projection/repacking,
reply-environment slots, branch dispatch, output projection, and signing-list cons.
All data-dependent scans and arithmetic are executed separately and charged below. -/
noncomputable def reply (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) :
    StateT (CacheState F M qS) ProbComp (Run G₁) := fun state => do
  let defaultInit := (Expr.op CryptoOp.zero .unit : Expr CryptoOp [] scalar).run
    (arithmetic F G₁ G₂ M M cost) ()
  let rho ← (cacheHandler (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq (Draw.scalar (qS := qS)) defaultInit.value m).run state.scalars
  let k ← (cacheHandler (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq (Draw.coin (qS := qS)) 0 m).run state.coins
  let coin := (coinValue qS).run (arithmetic F G₁ G₂ M M cost) (k.1.value, ())
  let result := if signing then
    signReply.run (arithmetic F G₁ G₂ M M cost) (rho.1.value, X, coin.value, ())
    else hashReply.run (arithmetic F G₁ G₂ M M cost) (rho.1.value, g, h, coin.value, ())
  pure (⟨result.value, rho.1.steps + k.1.steps + coin.steps + result.steps + defaultInit.steps + 24⟩,
    ⟨rho.2, k.2, if signing then m :: state.signed else state.signed⟩)

def replyBase (cost : PrimitiveCosts) (sampling : SamplingCosts) (signing : Bool) : Nat :=
  sampling.scalar + sampling.coin + cost.field + cost.scalar₁ + 2 * cost.natOp +
    (if signing then cost.group + 112 else 2 * cost.group + 118)

theorem reply_bound (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (state : CacheState F M qS)
    (z : Run G₁ × CacheState F M qS)
    (hz : z ∈ support ((reply (G₂ := G₂) cost sampling g X h qS signing m).run state)) :
    z.2.size ≤ state.size + 1 ∧
      z.1.steps ≤ replyBase cost sampling signing + 2 * (cost.messageEq + 19) * state.size := by
  simp only [reply, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨rho, hrho, coin, hcoin, rfl⟩ := hz
  have hrt := cacheHandler_steps_le (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.scalar cost.messageEq sampling.scalar (fun _ _ => le_rfl)
    (fun r hr => (draws_steps qS sampling Draw.scalar () r hr).le) m 0 state.scalars rho hrho
  have hct := cacheHandler_steps_le (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.coin cost.messageEq sampling.coin (fun _ _ => le_rfl)
    (fun r hr => (draws_steps qS sampling Draw.coin () r hr).le) m 0 state.coins coin hcoin
  have hrl := cacheHandler_length (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.scalar (fun _ _ => rfl) m 0 state.scalars rho hrho
  have hcl := cacheHandler_length (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.coin (fun _ _ => rfl) m 0 state.coins coin hcoin
  have hrs : state.scalars.length ≤ state.size := Nat.le_max_left _ _
  have hcs : state.coins.length ≤ state.size :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hss : state.signed.length ≤ state.size :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hmr := Nat.mul_le_mul_right (cost.messageEq + 19) hrs
  have hmc := Nat.mul_le_mul_right (cost.messageEq + 19) hcs
  have hcv := coinValue_run (F := F) (G₁ := G₁) (G₂ := G₂) (M := M) cost qS coin.1.value
  have hzero : ((Expr.op CryptoOp.zero .unit : Expr CryptoOp [] scalar).run
      (arithmetic F G₁ G₂ M M cost) ()).steps = cost.field + 2 := by
    simp [Expr.run, arithmetic, CryptoOp.price]
    omega
  constructor
  · cases signing <;> simp only [Bool.false_eq_true, ite_false, ite_true, CacheState.size,
      List.length_cons] <;> omega
  · cases signing
    · have hb := hashReply_steps (G₂ := G₂) (M := M) cost rho.1.value g h coin.1.value.val
      simp only [Bool.false_eq_true, ite_false, replyBase, hcv, hzero]
      nlinarith
    · have hb := signReply_steps (G₂ := G₂) (M := M) cost rho.1.value X coin.1.value.val
      simp only [ite_true, replyBase, hcv, hzero]
      nlinarith

noncomputable def handler (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) :
    HandlerM (cryptoBase F G₁ G₂ M M) (Command randomBound)
      (StateT (CacheState F M qS) ProbComp) := fun cmd arg => match cmd with
  | .random n => fun state =>
      (fun x => (⟨x, sampling.random + 4⟩, state)) <$>
        (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1)))
  | .hash => reply (G₂ := G₂) cost sampling g X h qS false arg
  | .sign => reply (G₂ := G₂) cost sampling g X h qS true arg

def replies (randomBound : Nat) : ReplyContract (cryptoBase F G₁ G₂ M M) (Command randomBound) where
  allows _ _ _ := True
  responds cmd _ := by
    cases cmd with
    | random n => exact ⟨0, trivial⟩
    | hash => exact ⟨0, trivial⟩
    | sign => exact ⟨0, trivial⟩

def prices (cost : PrimitiveCosts) (sampling : SamplingCosts) (k : Fin 3) : Nat :=
  if k = 0 then sampling.random + 4 else replyBase cost sampling (k == 2)

/-- Adaptive runtime bound for the implemented lazy simulation, including cache hits and
signing-log allocation. Initialization, the final verification hash and extraction are
separate until the finished reduction certificate is assembled. -/
theorem simulation_bound (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ a}
    (code : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ M M cost) (replies randomBound) kind
      code env localTime queries)
    (z : Run (a.Value (cryptoBase F G₁ G₂ M M)) × CacheState F M qS)
    (hz : z ∈ support ((code.run (arithmetic F G₁ G₂ M M cost)
      (handler cost sampling g X h qS randomBound) env).run .empty)) :
    z.2.size ≤ ∑ k, queries k ∧
      z.1.steps ≤ localTime + (∑ k, queries k * prices cost sampling k) +
        2 * (cost.messageEq + 19) * (∑ k, queries k) ^ 2 := by
  have hb := SourceBudget.linear_state_bound (arithmetic F G₁ G₂ M M cost) (replies randomBound) kind
    code env localTime queries hsource (handler cost sampling g X h qS randomBound)
    (prices cost sampling) (2 * (cost.messageEq + 19)) (fun _ => True) CacheState.size (by
      intro a b cmd arg state _ out hout
      refine ⟨trivial, trivial, ?_⟩
      cases cmd with
      | random n =>
          simp only [handler, StateT.run, support_map, Set.mem_image] at hout
          obtain ⟨r, _, rfl⟩ := hout
          simp [kind, prices]
      | hash =>
          have hstep := reply_bound (G₂ := G₂) cost sampling g X h qS false arg state out hout
          simpa [kind, prices] using hstep
      | sign =>
          have hstep := reply_bound (G₂ := G₂) cost sampling g X h qS true arg state out hout
          simpa [kind, prices] using hstep)
    .empty trivial rfl z hz
  exact hb.2

end Signatures.Runtime.Coron
