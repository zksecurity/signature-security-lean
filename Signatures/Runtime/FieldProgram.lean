import Signatures.Runtime.PrimeFieldOps

/-! Straight-line field code compiled to the verified prime-field circuits.
Explicit bindings share intermediate wires. Both arms of a selection are built,
so the gate bound is independent of secret values. -/

namespace Signatures.Runtime.FieldProgram

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open PrimeFieldCircuit (Built Represents)

inductive BinOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

def BinOp.eval {F : Type} [Field F] : BinOp → F → F → F
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

def BinOp.gates (w : Nat) : BinOp → Nat
  | .add => 36 * w * w + 19 * w
  | .sub => 36 * w * w + 43 * w
  | .mul => 51 * w * w + 7 * w
  | .div => 2 * (51 * w * w + 7 * w) * w + (51 * w * w + 7 * w)

inductive Code : Nat → Type where
  | var {n} : Fin n → Code n
  | lit {n} : Nat → Code n
  | binary {n} : BinOp → Code n → Code n → Code n
  | bind {n} : Code n → Code (n + 1) → Code n
  | iteEq {n} : Fin n → Fin n → Code n → Code n → Code n
  deriving Repr

def Code.eval {F : Type} [Field F] [DecidableEq F] {n : Nat} : Code n → (Fin n → F) → F
  | .var i, env => env i
  | .lit x, _ => x
  | .binary op x y, env => op.eval (x.eval env) (y.eval env)
  | .bind x body, env => body.eval (Fin.cases (x.eval env) env)
  | .iteEq i j yes no, env => if env i = env j then yes.eval env else no.eval env

def Code.gates (w : Nat) {n : Nat} : Code n → Nat
  | .var _ | .lit _ => 0
  | .binary op x y => x.gates w + y.gates w + op.gates w
  | .bind x body => x.gates w + body.gates w
  | .iteEq _ _ yes no => yes.gates w + no.gates w + 7 * w

instance {n : Nat} : Add (Code n) := ⟨.binary .add⟩
instance {n : Nat} : Sub (Code n) := ⟨.binary .sub⟩
instance {n : Nat} : Mul (Code n) := ⟨.binary .mul⟩
instance {n : Nat} : Div (Code n) := ⟨.binary .div⟩
instance {n : Nat} : Neg (Code n) := ⟨fun x => .binary .sub (.lit 0) x⟩
instance {n : Nat} (k : Nat) : OfNat (Code n) k := ⟨.lit k⟩

@[simp] theorem Code.eval_add {F : Type} [Field F] [DecidableEq F] {n : Nat}
    (x y : Code n) (env : Fin n → F) : (x + y).eval env = x.eval env + y.eval env := rfl
@[simp] theorem Code.eval_sub {F : Type} [Field F] [DecidableEq F] {n : Nat}
    (x y : Code n) (env : Fin n → F) : (x - y).eval env = x.eval env - y.eval env := rfl
@[simp] theorem Code.eval_mul {F : Type} [Field F] [DecidableEq F] {n : Nat}
    (x y : Code n) (env : Fin n → F) : (x * y).eval env = x.eval env * y.eval env := rfl
@[simp] theorem Code.eval_div {F : Type} [Field F] [DecidableEq F] {n : Nat}
    (x y : Code n) (env : Fin n → F) : (x / y).eval env = x.eval env / y.eval env := rfl
@[simp] theorem Code.eval_neg {F : Type} [Field F] [DecidableEq F] {n : Nat}
    (x : Code n) (env : Fin n → F) : (-x).eval env = -x.eval env := by
  change ((0 : Nat) : F) - x.eval env = _
  simp

@[simp] theorem Code.gates_add {n : Nat} (x y : Code n) (w : Nat) :
    (x + y).gates w = x.gates w + y.gates w + BinOp.add.gates w := rfl
@[simp] theorem Code.gates_sub {n : Nat} (x y : Code n) (w : Nat) :
    (x - y).gates w = x.gates w + y.gates w + BinOp.sub.gates w := rfl
@[simp] theorem Code.gates_mul {n : Nat} (x y : Code n) (w : Nat) :
    (x * y).gates w = x.gates w + y.gates w + BinOp.mul.gates w := rfl
@[simp] theorem Code.gates_div {n : Nat} (x y : Code n) (w : Nat) :
    (x / y).gates w = x.gates w + y.gates w + BinOp.div.gates w := rfl
@[simp] theorem Code.gates_neg {n : Nat} (x : Code n) (w : Nat) :
    (-x).gates w = x.gates w + BinOp.sub.gates w := by
  change 0 + x.gates w + _ = _
  omega

def Code.rename {n m : Nat} (f : Fin n → Fin m) : Code n → Code m
  | .var i => .var (f i)
  | .lit x => .lit x
  | .binary op x y => .binary op (x.rename f) (y.rename f)
  | .bind x body => .bind (x.rename f) (body.rename (Fin.cases 0 (fun i => (f i).succ)))
  | .iteEq i j yes no => .iteEq (f i) (f j) (yes.rename f) (no.rename f)

theorem Code.eval_rename {F : Type} [Field F] [DecidableEq F] {n m : Nat}
    (code : Code n) (f : Fin n → Fin m) (env : Fin m → F) :
    (code.rename f).eval env = code.eval (fun i => env (f i)) := by
  induction code generalizing m with
  | var => rfl
  | lit => rfl
  | binary op x y ihx ihy => simp only [rename, eval, ihx, ihy]
  | bind x body ihx ihbody =>
    simp only [rename, eval, ihx, ihbody]
    congr 1
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  | iteEq i j yes no iht ihf => simp only [rename, eval, iht, ihf]

theorem Code.gates_rename {n m : Nat} (code : Code n) (f : Fin n → Fin m) (w : Nat) :
    (code.rename f).gates w = code.gates w := by
  induction code generalizing m with
  | var => rfl
  | lit => rfl
  | binary op x y ihx ihy => simp only [rename, gates, ihx, ihy]
  | bind x body ihx ihbody => simp only [rename, gates, ihx, ihbody]
  | iteEq i j yes no iht ihf => simp only [rename, gates, iht, ihf]

/-- General field comparison, sharing both compared expressions through bindings. -/
def Code.ifEq {n : Nat} (x y yes no : Code n) : Code n :=
  .bind x (.bind (y.rename Fin.succ) (.iteEq (Fin.succ 0) 0
    (yes.rename (fun i => i.succ.succ)) (no.rename (fun i => i.succ.succ))))

theorem Code.eval_ifEq {F : Type} [Field F] [DecidableEq F] {n : Nat}
    (x y yes no : Code n) (env : Fin n → F) :
    (Code.ifEq x y yes no).eval env =
      if x.eval env = y.eval env then yes.eval env else no.eval env := by
  simp only [ifEq, eval, eval_rename, Fin.cases_succ, Fin.cases_zero]

theorem Code.gates_ifEq {n : Nat} (x y yes no : Code n) (w : Nat) :
    (Code.ifEq x y yes no).gates w = x.gates w + y.gates w +
      yes.gates w + no.gates w + 7 * w := by
  simp only [ifEq, gates, gates_rename, Nat.add_assoc]

variable {A : Type} [Hashable A] [DecidableEq A] {w : Nat}

def binary (op : BinOp) (p : Nat) (aig : AIG A) (input : AIG.BinaryRefVec aig w) : Built aig w :=
  match op with
  | .add => PrimeFieldCircuit.add aig input p
  | .sub => PrimeFieldCircuit.subtract aig input p
  | .mul => PrimeFieldCircuit.multiply aig input p
  | .div =>
    let inv := PrimeFieldCircuit.inverse aig input.rhs p
    inv.chain (PrimeFieldCircuit.multiply inv.result.aig ⟨inv.cast input.lhs, inv.result.vec⟩ p)

def choose (aig : AIG A) (x y yes no : AIG.RefVec aig w) : Built aig w :=
  let eq := BVPred.mkEq aig ⟨x, y⟩
  let he := AIG.LawfulOperator.isPrefix_aig (f := BVPred.mkEq) aig ⟨x, y⟩
  let args := AIG.RefVec.IfInput.mk eq.ref (yes.cast he.size_le) (no.cast he.size_le)
  let out := AIG.RefVec.ite eq.aig args
  let hi := AIG.LawfulVecOperator.isPrefix_aig (f := AIG.RefVec.ite) eq.aig args
  ⟨out, ⟨he.size_le.trans hi.size_le,
    fun i h => (hi.idx_eq i (h.trans_le he.size_le)).trans (he.idx_eq i h)⟩⟩

theorem choose_size (aig : AIG A) (x y yes no : AIG.RefVec aig w) :
    (choose aig x y yes no).result.aig.decls.size ≤ aig.decls.size + 7 * w := by
  unfold choose
  dsimp only
  refine (BitCircuit.ite_size _ _).trans ?_
  have := BitCircuit.eq_size aig ⟨x, y⟩
  omega

theorem choose_correct (aig : AIG A) (x y yes no : AIG.RefVec aig w) (assign : A → Bool)
    (vx vy vt vf : BitVec w) (hx : Represents assign aig x vx)
    (hy : Represents assign aig y vy) (ht : Represents assign aig yes vt)
    (hf : Represents assign aig no vf) :
    Represents assign (choose aig x y yes no).result.aig (choose aig x y yes no).result.vec
      (if vx = vy then vt else vf) := by
  intro i hi
  unfold choose
  rw [AIG.RefVec.denote_ite]
  dsimp only
  rw [BVPred.mkEq_denote_eq aig ⟨x, y⟩ assign vx vy hx hy]
  rw [AIG.RefVec.get_cast, AIG.RefVec.get_cast,
    AIG.LawfulOperator.denote_cast_entry (f := BVPred.mkEq) ⟨aig, yes.get i hi⟩,
    AIG.LawfulOperator.denote_cast_entry (f := BVPred.mkEq) ⟨aig, no.get i hi⟩, ht i hi, hf i hi]
  by_cases h : vx = vy <;> simp [h]

variable {p : Nat} [Fact p.Prime]

theorem binary_size (hfit : p * p ≤ 2 ^ w) (op : BinOp) (aig : AIG A)
    (input : AIG.BinaryRefVec aig w) :
    (binary op p aig input).result.aig.decls.size ≤ aig.decls.size + op.gates w := by
  cases op with
  | add => simpa only [binary, BinOp.gates, Nat.add_assoc] using PrimeFieldCircuit.add_size aig input p
  | sub => simpa only [binary, BinOp.gates, Nat.add_assoc] using PrimeFieldCircuit.subtract_size aig input p
  | mul => simpa only [binary, PrimeFieldCircuit.multiply, BinOp.gates, Nat.add_assoc] using
      PrimeFieldCircuit.mulMod_size aig input p
  | div => simpa only [binary, Built.chain, PrimeFieldCircuit.multiply, PrimeFieldCircuit.divide,
      BinOp.gates, Nat.add_assoc] using PrimeFieldCircuit.divide_size hfit aig input.lhs input.rhs

theorem binary_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (op : BinOp) (aig : AIG A)
    (input : AIG.BinaryRefVec aig w) (assign : A → Bool) (x y : ZMod p)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x.val))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y.val)) :
    Represents assign (binary op p aig input).result.aig (binary op p aig input).result.vec
      (BitVec.ofNat w (op.eval x y).val) := by
  cases op with
  | add => exact PrimeFieldCircuit.add_correct hfit aig input assign x y hx hy
  | sub => exact PrimeFieldCircuit.subtract_correct hfit aig input assign x y hx hy
  | mul => exact PrimeFieldCircuit.mulMod_correct hfit aig input assign x y hx hy
  | div => exact PrimeFieldCircuit.divide_correct hfit hp aig input.lhs input.rhs assign x y hx hy

attribute [local irreducible] binary choose

def Code.compile (p : Nat) {n : Nat} : (code : Code n) →
    (aig : AIG A) → (Fin n → AIG.RefVec aig w) → Built aig w
  | .var i, aig, env => ⟨⟨aig, env i⟩, AIG.IsPrefix.rfl⟩
  | .lit x, aig, _ => ⟨⟨aig, blastConst aig (BitVec.ofNat w (x % p))⟩, AIG.IsPrefix.rfl⟩
  | .binary op x y, aig, env =>
    let lhs := x.compile p aig env
    let rhs := y.compile p lhs.result.aig (fun i => lhs.cast (env i))
    lhs.chain (rhs.chain (FieldProgram.binary op p rhs.result.aig ⟨rhs.cast lhs.result.vec, rhs.result.vec⟩))
  | .bind x body, aig, env =>
    let value := x.compile p aig env
    value.chain (body.compile p value.result.aig (Fin.cases value.result.vec (fun i => value.cast (env i))))
  | .iteEq i j yes no, aig, env =>
    let yt := yes.compile p aig env
    let nf := no.compile p yt.result.aig (fun i => yt.cast (env i))
    yt.chain (nf.chain (choose nf.result.aig (nf.cast (yt.cast (env i)))
      (nf.cast (yt.cast (env j))) (nf.cast yt.result.vec) nf.result.vec))

theorem Code.compile_size (hfit : p * p ≤ 2 ^ w) {n : Nat} (code : Code n)
    (aig : AIG A) (env : Fin n → AIG.RefVec aig w) :
    (code.compile p aig env).result.aig.decls.size ≤ aig.decls.size + code.gates w := by
  induction code generalizing aig with
  | var => simp [compile, gates]
  | lit => simp [compile, gates]
  | binary op x y ihx ihy =>
    dsimp only [compile, Built.chain, gates]
    refine (binary_size hfit _ _ _).trans ?_
    have hx := ihx aig env
    have hy := ihy (x.compile p aig env).result.aig (fun i => (x.compile p aig env).cast (env i))
    omega
  | bind x body ihx ihbody =>
    dsimp only [compile, Built.chain, gates]
    refine (ihbody _ _).trans ?_
    have := ihx aig env
    omega
  | iteEq i j yes no ihyes ihno =>
    dsimp only [compile, Built.chain, gates]
    refine (choose_size _ _ _ _ _).trans ?_
    have hy := ihyes aig env
    have hn := ihno (yes.compile p aig env).result.aig
      (fun i => (yes.compile p aig env).cast (env i))
    omega

theorem Code.compile_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) {n : Nat} (code : Code n)
    (aig : AIG A) (env : Fin n → AIG.RefVec aig w) (assign : A → Bool) (values : Fin n → ZMod p)
    (h : ∀ i, Represents assign aig (env i) (BitVec.ofNat w (values i).val)) :
    Represents assign (code.compile p aig env).result.aig (code.compile p aig env).result.vec
      (BitVec.ofNat w (code.eval values).val) := by
  induction code generalizing aig with
  | var i => exact h i
  | lit x => simpa only [compile, Represents, eval, ZMod.val_natCast] using
      denote_blastConst aig (BitVec.ofNat w (x % p)) assign
  | binary op x y ihx ihy =>
    let lhs := x.compile p aig env
    let rhs := y.compile p lhs.result.aig (fun i => lhs.cast (env i))
    exact binary_correct hfit hp op rhs.result.aig _ assign _ _
      (rhs.preserves assign lhs.result.vec _ (ihx aig env values h))
      (ihy lhs.result.aig _ values (fun i => lhs.preserves assign (env i) _ (h i)))
  | bind x body ihx ihbody =>
    let value := x.compile p aig env
    apply ihbody value.result.aig _ (Fin.cases (x.eval values) values)
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ihx aig env values h
    · exact value.preserves assign (env j) _ (h j)
  | iteEq i j yes no ihyes ihno =>
    let yt := yes.compile p aig env
    let nf := no.compile p yt.result.aig (fun i => yt.cast (env i))
    have he := choose_correct nf.result.aig _ _ _ _ assign
      (BitVec.ofNat w (values i).val) (BitVec.ofNat w (values j).val)
      (BitVec.ofNat w (yes.eval values).val) (BitVec.ofNat w (no.eval values).val)
      (nf.preserves assign _ _ (yt.preserves assign _ _ (h i)))
      (nf.preserves assign _ _ (yt.preserves assign _ _ (h j)))
      (nf.preserves assign _ _ (ihyes aig env values h))
      (ihno yt.result.aig _ values (fun i => yt.preserves assign _ _ (h i)))
    have hmod : p ≤ 2 ^ w := (Nat.le_mul_self p).trans hfit
    have hi := (PrimeFieldCircuit.encoding_injective hmod).eq_iff (a := values i) (b := values j)
    simpa only [compile, Built.chain, hi, eval, apply_ite, yt, nf] using he

end Signatures.Runtime.FieldProgram
