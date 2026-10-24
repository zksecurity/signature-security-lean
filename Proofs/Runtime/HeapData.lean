import Proofs.Runtime.HeapArguments
import Proofs.Runtime.Data

/-! Data loading reuses the bit-expression controller. Encoding specifies the
input representation or prepares fixed constants offline. The online loader
only copies bit words and allocates shared nodes; it never decodes group values. -/

namespace Signatures.Runtime.HeapData

open HeapBits SharedHeap HeapExpression WeierstrassCurve

variable {r p₁ p₂ w : Nat} [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)

def encode : (a : Ty CryptoAtom) → a.Value (cryptoBase (ZMod r) H₁ H₂ K M) → HeapExpression.Code
  | .atom _, x => .word (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x)
  | .unit, _ => .word []
  | .bool, b => .word [b]
  | .nat, n => .word (natBits w n)
  | .pair a b, x => .pair (encode a x.1) (encode b x.2)
  | .list a, xs => xs.foldr (fun x tail => .cons (encode a x) tail) .nil

/-- The width premise includes natural and `Fin` leaves. A unit-priced source
atom by itself does not imply that its representation fits the chosen width. -/
theorem encode_spec (a : Ty CryptoAtom) (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (heap : List Node) (store : Store) (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (hx : NaturalRange.ValueBound w x) :
    ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) heap (a.load x).steps x
      ((encode H₁ H₂ encodeK encodeM a x).run [] store) := by
  induction a generalizing heap store with
  | atom a =>
    apply alloc_spec store hs hw (.word (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x))
      ?_ x (.atom (alloc_lookup store heap hs _) ⟨rfl, hx⟩)
    change (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x).length ≤ 3*w+1
    rw [portBits_length H₁ H₂ encodeK encodeM (.atom a) x]
    cases a <;> simp only [FixedPorts.Layout.width] <;> omega
  | unit =>
    cases x
    exact alloc_spec (t := .unit) store hs hw (.word []) (by simp [NodeBound]) ()
      (.unit (alloc_lookup store heap hs _))
  | bool =>
    exact alloc_spec store hs hw (.word [x]) (by simp [NodeBound]) x
      (.bool (alloc_lookup store heap hs _))
  | nat =>
    exact (alloc_spec store hs hw (.word (natBits w x)) (by simp [NodeBound, natBits]; omega)
      x (.nat (alloc_lookup store heap hs _) hx)).mono (by simp [Ty.load])
  | pair a b ihl ihr =>
    have h : ResultSpec (t := .pair a b) w (3*w+1) (atomRep (r := r) H₁ H₂ encodeK encodeM) heap
        ((a.load x.1).steps+((b.load x.2).steps+1)) x
        ((encode H₁ H₂ encodeK encodeM (.pair a b) x).run [] store) := by
      apply bind_spec (ihl x.1 heap store hs hw hx.1)
      intro extra left s₁ _ hs₁ hw₁ hl _
      apply bind_spec (ihr x.2 (heap ++ extra) s₁ hs₁ hw₁ hx.2)
      intro more right s₂ _ hs₂ hw₂ hr _
      have hl' := hl.append more
      exact alloc_spec s₂ hs₂ hw₂ (.pair left right) ⟨hl'.address_lt, hr.address_lt⟩ x
        (alloc_pair s₂ hs₂ hl' hr)
    simpa only [encode, Code.run, Ty.load, Nat.add_assoc] using h
  | list a ih =>
    induction x generalizing heap store with
    | nil => exact alloc_spec (t := .list a) store hs hw .nil trivial [] (.nil (alloc_lookup store heap hs _))
    | cons x xs iht =>
      have hh := hx x (by simp)
      have ht : NaturalRange.ValueBound (t := .list a) w xs := fun y hy => hx y (by simp [hy])
      have h : ResultSpec (t := .list a) w (3*w+1) (atomRep (r := r) H₁ H₂ encodeK encodeM) heap
          ((a.load x).steps+(((Ty.list a).load xs).steps+1)) (x :: xs)
          ((encode H₁ H₂ encodeK encodeM (.list a) (x :: xs)).run [] store) := by
        apply bind_spec (ih x heap store hs hw hh)
        intro extra head s₁ _ hs₁ hw₁ hhead _
        apply bind_spec (iht (heap ++ extra) s₁ hs₁ hw₁ ht)
        intro more tail s₂ _ hs₂ hw₂ htail _
        have hhead' := hhead.append more
        exact alloc_spec s₂ hs₂ hw₂ (.cons head tail) ⟨hhead'.address_lt, htail.address_lt⟩ _
          (alloc_cons s₂ hs₂ hhead' htail)
      simpa only [encode, List.foldr_cons, Code.run, Ty.load, Nat.add_assoc] using h

def factor (w nodes : Nat) := allocBudget (3*w+1) nodes + 3

/-- Copying all data words, allocating structure and sequencing are charged.
The source load size bounds allocation, but bit width remains explicit. -/
theorem encode_steps (a : Ty CryptoAtom) (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (heap : List Node) (store : Store) (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (hx : NaturalRange.ValueBound w x) (nodes : Nat) (hn : heap.length+(a.load x).steps ≤ nodes) :
    ((encode H₁ H₂ encodeK encodeM a x).run [] store).steps ≤ (a.load x).steps*factor w nodes := by
  have spec (a : Ty CryptoAtom) x heap store hs hw hx :=
    encode_spec (r := r) H₁ H₂ encodeK encodeM a x heap store hs hw hx
  induction a generalizing heap store with
  | atom a =>
    have hsize : NodeBound (3*w+1) heap.length (.word (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x)) := by
      change (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x).length ≤ 3*w+1
      rw [portBits_length H₁ H₂ encodeK encodeM (.atom a) x]
      cases a <;> simp only [FixedPorts.Layout.width] <;> omega
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs _ hsize
    simp only [encode, Code.run, lift, Ty.load, Nat.one_mul, factor]
    omega
  | unit =>
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs (.word []) (by simp [NodeBound])
    simp only [encode, Code.run, lift, Ty.load, Nat.one_mul, factor]
    omega
  | bool =>
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs (.word [x]) (by simp [NodeBound])
    simp only [encode, Code.run, lift, Ty.load, Nat.one_mul, factor]
    omega
  | nat =>
    have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs (.word (natBits w x))
      (by simp [NodeBound, natBits]; omega)
    simp only [encode, Code.run, lift, Ty.load, factor]
    nlinarith
  | pair a b ihl ihr =>
    simp only [Ty.load] at hn ⊢
    have h : ((encode H₁ H₂ encodeK encodeM (.pair a b) x).run [] store).steps ≤
        (a.load x.1).steps*factor w nodes +
          ((b.load x.2).steps*factor w nodes+allocBudget (3*w+1) nodes+2)+1 := by
      apply bind_steps_spec (spec a x.1 heap store hs hw hx.1)
        (ihl x.1 heap store hs hw hx.1 (by omega))
      intro extra left s₁ _ hs₁ hw₁ hl hlen
      apply (bind_steps_spec (nextCost := allocBudget (3*w+1) nodes+1)
        (spec b x.2 _ s₁ hs₁ hw₁ hx.2)
        (ihr x.2 _ s₁ hs₁ hw₁ hx.2 (by simp only [List.length_append]; omega)) ?_).trans (by omega)
      intro more right s₂ _ hs₂ hw₂ hr hmore
      have hl' := hl.append more
      have ha := alloc_le_budget hw₂ (show ((heap ++ extra) ++ more).length ≤ nodes by
        simp only [List.length_append]; omega) s₂ hs₂ (.pair left right) ⟨hl'.address_lt, hr.address_lt⟩
      exact Nat.add_le_add_right ha 1
    simp only [Nat.add_mul, Nat.one_mul]
    dsimp only [factor] at h ⊢
    omega
  | list a ih =>
    induction x generalizing heap store with
    | nil =>
      have h := alloc_le_budget hw (show heap.length ≤ nodes by omega) store hs .nil trivial
      simp only [encode, List.foldr_nil, Code.run, lift, Ty.load, Nat.one_mul, factor]
      omega
    | cons x xs iht =>
      have hh := hx x (by simp)
      have ht : NaturalRange.ValueBound (t := .list a) w xs := fun y hy => hx y (by simp [hy])
      change heap.length+((a.load x).steps+((Ty.list a).load xs).steps+1) ≤ nodes at hn
      have h : ((encode H₁ H₂ encodeK encodeM (.list a) (x :: xs)).run [] store).steps ≤
          (a.load x).steps*factor w nodes +
            (((Ty.list a).load xs).steps*factor w nodes+allocBudget (3*w+1) nodes+2)+1 := by
        apply bind_steps_spec (spec a x heap store hs hw hh)
          (ih x heap store hs hw hh (by omega))
        intro extra head s₁ _ hs₁ hw₁ hhead hlen
        apply (bind_steps_spec (nextCost := allocBudget (3*w+1) nodes+1)
          (spec (.list a) xs _ s₁ hs₁ hw₁ ht)
          (iht _ s₁ hs₁ hw₁ ht (by simp only [List.length_append]; omega)) ?_).trans (by omega)
        intro more tail s₂ _ hs₂ hw₂ htail hmore
        have hhead' := hhead.append more
        have ha := alloc_le_budget hw₂ (show ((heap ++ extra) ++ more).length ≤ nodes by
          simp only [List.length_append]; omega) s₂ hs₂ (.cons head tail) ⟨hhead'.address_lt, htail.address_lt⟩
        exact Nat.add_le_add_right ha 1
      change _ ≤ ((a.load x).steps+((Ty.list a).load xs).steps+1)*factor w nodes
      simp only [Nat.add_mul, Nat.one_mul]
      dsimp only [factor] at h ⊢
      omega

def encodeEnv : {Γ : List (Ty CryptoAtom)} → Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ →
    List HeapExpression.Code
  | [], _ => []
  | a :: _, env => encode H₁ H₂ encodeK encodeM a env.1 :: encodeEnv env.2

def envFactor (w nodes registers : Nat) :=
  max (factor w nodes) (frameBudget registers nodes + 3)

/-- The existing argument-frame loader also handles input and fixed-data
registers. Its bound includes construction of the encoded register spine. -/
theorem encodeEnv_costed {Γ : List (Ty CryptoAtom)}
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (heap : List Node) (store : Store)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : NaturalRange.EnvBound w env) (nodes registers : Nat)
    (hn : heap.length+(Env.load env).steps ≤ nodes) (hregs : Γ.length ≤ registers) :
    HeapArguments.ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) heap
      (Env.load env).steps env (HeapArguments.run (encodeEnv H₁ H₂ encodeK encodeM env) [] store) ∧
    (HeapArguments.run (encodeEnv H₁ H₂ encodeK encodeM env) [] store).steps ≤
      (Env.load env).steps*envFactor w nodes registers := by
  induction Γ generalizing heap store with
  | nil =>
    refine ⟨⟨[], [], store, rfl, ?_, ?_, .nil, by simp [Env.load]⟩, ?_⟩
    · simpa using hs
    · simpa using hw
    · simpa only [encodeEnv, HeapArguments.run, Env.load, Nat.one_mul, envFactor] using
        ((by dsimp [factor]; omega : 1 ≤ factor w nodes).trans
          (le_max_left _ (frameBudget registers nodes+3)))
  | cons a Γ ih =>
    simp only [Env.load] at hn
    have hhead := encode_spec H₁ H₂ encodeK encodeM a env.1 heap store hs hw he.1
    have hcost := encode_steps H₁ H₂ encodeK encodeM a env.1 heap store hs hw he.1 nodes (by omega)
    have hcost := hcost.trans (Nat.mul_le_mul_left _ (le_max_left _ (frameBudget registers nodes+3)))
    obtain ⟨extra, root, next, hv, hs₁, hw₁, hx, hlen⟩ := hhead
    obtain ⟨htail, htailCost⟩ := ih env.2 (heap ++ extra) next hs₁ hw₁ he.2
      (by simp only [List.length_append]; omega) (by simp only [List.length_cons] at hregs; omega)
    obtain ⟨more, output, finalStore, htval, hs₂, hw₂, hout, hmore⟩ := htail
    have hx' := hx.append more
    have hsize : ((heap ++ extra) ++ more).length ≤ nodes := by
      simp only [List.length_append]; omega
    have hpush := framePush_le_budget (registers := registers) output root
      (fun addr h => (hout.addresses addr h).trans_le hsize)
      (hx'.address_lt.trans_le hsize) (by rw [hout.length]; simp only [List.length_cons] at hregs; omega)
    constructor
    · refine ⟨extra ++ more, root :: output, finalStore, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [encodeEnv, HeapArguments.run, HeapExpression.bind, hv, htval, framePush_value]
      · simpa only [List.append_assoc] using hs₂
      · simpa only [List.append_assoc] using hw₂
      · simpa only [List.append_assoc] using EnvRep.cons hx' hout
      · simp only [List.length_append, Env.load]; omega
    · have hf : frameBudget registers nodes+3 ≤ envFactor w nodes registers := le_max_right _ _
      simp only [encodeEnv, HeapArguments.run, HeapExpression.bind, hv, htval, Env.load,
        Nat.add_mul, Nat.one_mul]
      change _ ≤ (a.load env.1).steps*envFactor w nodes registers at hcost
      omega

end Signatures.Runtime.HeapData
