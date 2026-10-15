import Signatures.Runtime.BackendAssembly

/-! Compositional all-path bounds for finite backend programs.

Every leaf obligation concerns actual local backend code or an external
primitive. Structural costs retain their encoded-size arguments. The loop rule
derives its complete bound from a preserved invariant and per-iteration bounds.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)

def Bounds {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (pre : A → Prop) (post : B → Prop) (budget : Nat) : Prop :=
  ∀ input, pre input → ∀ z ∈ support (code.run control queryCost input),
    post z.value ∧ z.steps ≤ budget

/-- Increase the time allowance while retaining the same actual program and
input/output invariants. This rule keeps large program syntax opaque in clients. -/
theorem Bounds.time_mono {A B : Type} {a : C.Str A} {b : C.Str B}
    {code : Code Q spec iface a b} {pre : A → Prop} {post : B → Prop} {budget larger : Nat}
    (bound : Bounds control queryCost code pre post budget) (increase : budget ≤ larger) :
    Bounds control queryCost code pre post larger := by
  intro input hi out ho
  obtain ⟨hp, ht⟩ := bound input hi out ho
  exact ⟨hp, ht.trans increase⟩

/-- Strengthen the input predicate and weaken the output predicate of the same
actual program without changing its time allowance. -/
theorem Bounds.consequence {A B : Type} {a : C.Str A} {b : C.Str B}
    {code : Code Q spec iface a b} {pre pre' : A → Prop} {post post' : B → Prop} {budget : Nat}
    (bound : Bounds control queryCost code pre post budget)
    (input : ∀ a, pre' a → pre a) (output : ∀ b, post b → post' b) :
    Bounds control queryCost code pre' post' budget := by
  intro arg hi out ho
  obtain ⟨hp, ht⟩ := bound arg (input arg hi) out ho
  exact ⟨output out.value hp, ht⟩

theorem Bounds.atomic {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) (pre : A → Prop) (post : B → Prop) (budget : Nat)
    (h : ∀ input, pre input → post (f input) ∧
      Q.cost code input + control.localCall (Q.size a input) (Q.size b (f input)) ≤ budget) :
    Bounds control queryCost (Code.atomic (iface := iface) code) pre post budget := by
  intro input hp z hz
  simp only [Code.run, support_pure, Set.mem_singleton_iff] at hz
  subst z
  exact h input hp

theorem Bounds.query (pre : I → Prop) (post : (Σ i, spec.Range i) → Prop) (budget : Nat)
    (h : ∀ i, pre i → ∀ reply, post ⟨i, reply⟩ ∧
      queryCost i reply + control.query (Q.size iface.position i)
        (Q.size iface.response ⟨i, reply⟩) ≤ budget) :
    Bounds control queryCost (Code.query (Q := Q) (iface := iface)) pre post budget := by
  intro input hp z hz
  simp only [Code.run, support_map, Set.mem_image] at hz
  obtain ⟨reply, _, rfl⟩ := hz
  exact h input hp reply

theorem Bounds.seq {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (initial : Code Q spec iface a b) (following : Code Q spec iface b d)
    (pre : A → Prop) (middle : B → Prop) (post : D → Prop)
    (initialTime followingTime joinTime : Nat)
    (hi : Bounds control queryCost initial pre middle initialTime)
    (hf : Bounds control queryCost following middle post followingTime)
    (hj : ∀ input, pre input → ∀ value, middle value →
      control.sequence (Q.size a input) (Q.size b value) ≤ joinTime) :
    Bounds control queryCost (.seq initial following) pre post
      (initialTime + followingTime + joinTime) := by
  intro input hp z hz
  simp only [Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  obtain ⟨hm, ht⟩ := hi input hp x hx
  obtain ⟨hpost, hu⟩ := hf x.value hm y hy
  have hc := hj input hp x.value hm
  exact ⟨hpost, by dsimp; omega⟩

theorem Bounds.branch {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (left : Code Q spec iface a d) (right : Code Q spec iface b d)
    (preLeft : A → Prop) (preRight : B → Prop) (post : D → Prop)
    (leftTime rightTime branchTime : Nat)
    (hl : Bounds control queryCost left preLeft post leftTime)
    (hr : Bounds control queryCost right preRight post rightTime)
    (hc : ∀ input, Sum.elim preLeft preRight input →
      control.branch (Q.size (StepClass.HasSum.sum a b) input) ≤ branchTime) :
    Bounds control queryCost (.branch left right) (Sum.elim preLeft preRight) post
      (max leftTime rightTime + branchTime) := by
  intro input hp z hz
  have hfee := hc input hp
  cases input with
  | inl value =>
      simp only [Code.run, chargeRun, support_map, Set.mem_image] at hz
      obtain ⟨r, hr', rfl⟩ := hz
      obtain ⟨hout, ht⟩ := hl value hp r hr'
      exact ⟨hout, by dsimp; omega⟩
  | inr value =>
      simp only [Code.run, chargeRun, support_map, Set.mem_image] at hz
      obtain ⟨r, hr', rfl⟩ := hz
      obtain ⟨hout, ht⟩ := hr value hp r hr'
      exact ⟨hout, by dsimp; omega⟩

theorem Bounds.first {A B S : Type} {a : C.Str A} {b : C.Str B}
    (saved : C.Str S) (body : Code Q spec iface a b)
    (pre : A → Prop) (post : B → Prop) (keep : S → Prop) (bodyTime retainTime : Nat)
    (hb : Bounds control queryCost body pre post bodyTime)
    (hc : ∀ state, keep state → ∀ output, post output →
      control.retain (Q.size saved state) (Q.size b output) ≤ retainTime) :
    Bounds control queryCost (.first saved body) (fun p => pre p.1 ∧ keep p.2)
      (fun p => post p.1 ∧ keep p.2) (bodyTime + retainTime) := by
  intro input hp z hz
  simp only [Code.run, retainRun, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨hout, ht⟩ := hb input.1 hp.1 r hr
  have hfee := hc input.2 hp.2 r.value hout
  exact ⟨⟨hout, hp.2⟩, by dsimp; omega⟩

theorem loopRun_bound {S B : Type} (inv : S → Prop) (post : B → Prop)
    (fee : Nat → S → Nat) (body : S → OracleComp spec (Run (B ⊕ S)))
    (stop : S → OracleComp spec (Run B)) (bodyTime stopTime tickTime fuel : Nat)
    (hb : ∀ state, inv state → ∀ z ∈ support (body state),
      Sum.elim post inv z.value ∧ z.steps ≤ bodyTime)
    (hs : ∀ state, inv state → ∀ z ∈ support (stop state), post z.value ∧ z.steps ≤ stopTime)
    (hc : ∀ count ≤ fuel, ∀ state, inv state → fee count state ≤ tickTime)
    (state : S) (hi : inv state) (z : Run B)
    (hz : z ∈ support (loopRun fee body stop fuel state)) :
    post z.value ∧ z.steps ≤ fuel * (bodyTime + tickTime) + stopTime + tickTime := by
  induction fuel generalizing state z with
  | zero =>
      simp only [loopRun, chargeRun, support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      obtain ⟨hout, ht⟩ := hs state hi r hr
      have hfee := hc 0 le_rfl state hi
      exact ⟨hout, by dsimp; omega⟩
  | succ fuel ih =>
      simp only [loopRun, mem_support_bind_iff] at hz
      obtain ⟨step, hstep, hz⟩ := hz
      obtain ⟨hpost, ht⟩ := hb state hi step hstep
      have hfee := hc (fuel + 1) le_rfl state hi
      cases hv : step.value with
      | inl output =>
          simp only [hv, support_pure, Set.mem_singleton_iff] at hz
          subst z
          refine ⟨by simpa [hv] using hpost, ?_⟩
          dsimp
          nlinarith
      | inr next =>
          simp only [hv, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨rest, hr, rfl⟩ := hz
          have hn : inv next := by simpa [hv] using hpost
          obtain ⟨hout, hu⟩ := ih (fun n hn => hc n (by omega)) next hn rest hr
          refine ⟨hout, ?_⟩
          dsimp
          nlinarith

theorem Bounds.loop {S B : Type} {s : C.Str S} {b : C.Str B}
    (body : Code Q spec iface s (StepClass.HasSum.sum b s)) (stop : Code Q spec iface s b)
    (inv : S → Prop) (post : B → Prop) (bodyTime stopTime tickTime fuel : Nat)
    (hb : Bounds control queryCost body inv (Sum.elim post inv) bodyTime)
    (hs : Bounds control queryCost stop inv post stopTime)
    (hc : ∀ count ≤ fuel, ∀ state, inv state → control.loop count (Q.size s state) ≤ tickTime) :
    Bounds control queryCost (.loop body stop fuel) inv post
      (fuel * (bodyTime + tickTime) + stopTime + tickTime) := by
  intro state hi z hz
  exact loopRun_bound inv post _ _ _ bodyTime stopTime tickTime fuel hb hs hc state hi z hz

theorem iterationRun_bound {S : Type} (inv : S → Prop)
    (fee : Nat → S → Nat) (body : S → OracleComp spec (Run S))
    (bodyTime tickTime count : Nat)
    (hb : ∀ state, inv state → ∀ z ∈ support (body state), inv z.value ∧ z.steps ≤ bodyTime)
    (hc : ∀ n ≤ count, ∀ state, inv state → fee n state ≤ tickTime)
    (state : S) (hi : inv state) (z : Run S)
    (hz : z ∈ support (iterationRun fee body count state)) :
    inv z.value ∧ z.steps ≤ count * (bodyTime + tickTime) + tickTime := by
  induction count generalizing state z with
  | zero =>
      simp only [iterationRun, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hi, by simpa using hc 0 le_rfl state hi⟩
  | succ count ih =>
      simp only [iterationRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨step, hstep, rest, hrest, rfl⟩ := hz
      obtain ⟨hinv, ht⟩ := hb state hi step hstep
      obtain ⟨hout, hu⟩ := ih (fun n hn => hc n (by omega)) step.value hinv rest hrest
      have hfee := hc (count + 1) le_rfl state hi
      exact ⟨hout, by dsimp; nlinarith⟩

/-- The bound is linear in the numerical iteration cap, not in its encoding
length. A polynomial-time application must separately bound this cap. -/
theorem Bounds.iterate {S : Type} {s : C.Str S} (counter : C.Str Nat)
    (body : Code Q spec iface s s) (inv : S → Prop) (bodyTime tickTime cap : Nat)
    (hb : Bounds control queryCost body inv inv bodyTime)
    (hc : ∀ n ≤ cap, ∀ state, inv state → control.loop n
      (Q.size (StepClass.HasProd.prod counter s) (n, state)) ≤ tickTime) :
    Bounds control queryCost (.iterate counter body) (fun p => p.1 ≤ cap ∧ inv p.2) inv
      (cap * (bodyTime + tickTime) + tickTime) := by
  intro input hp z hz
  obtain ⟨hout, ht⟩ := iterationRun_bound inv _ _ bodyTime tickTime input.1 hb
    (fun n hn => hc n (hn.trans hp.1)) input.2 hp.2 z hz
  exact ⟨hout, ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hp.1) _)⟩

end Signatures.Runtime.BackendProgram
