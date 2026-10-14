import Signatures.Runtime.AttachTable
import Signatures.Runtime.BackendDataSize

/-! Reachable accumulator and representation bounds for positional attachment.
The invariant reserves one counter increment and one output row for every
remaining key, and permits arbitrary repeated keys and coefficient lengths. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.AttachCompiler

open AGM

def Remaining {I V : Type} (valid : I → Prop) (cap remaining : Nat)
    (acc : Nat × List (I × V)) : Prop :=
  acc.1 + remaining ≤ cap ∧ acc.2.length + remaining ≤ cap ∧
    ∀ row ∈ acc.2, valid row.1

theorem remaining_step {I V : Type} (valid : I → Prop) (cap remaining : Nat)
    (default : V) (values : List V) (i : I) (hi : valid i)
    (acc : Nat × List (I × V)) (ha : Remaining valid cap (remaining + 1) acc) :
    Remaining valid cap remaining (attachStep default values acc i) := by
  refine ⟨by dsimp only [attachStep]; have := ha.1; omega,
    by dsimp only [attachStep]; simp only [List.length_cons]; have := ha.2.1; omega, ?_⟩
  intro row hr
  rcases List.mem_cons.mp hr with hr | hr
  · subst row; exact hi
  · exact ha.2.2 row hr

theorem remaining_fold {I V : Type} (valid : I → Prop) (cap : Nat)
    (default : V) (values : List V) (keys : List I) (hk : ∀ i ∈ keys, valid i)
    (acc : Nat × List (I × V)) (ha : Remaining valid cap keys.length acc) :
    Remaining valid cap 0 (keys.foldl (attachStep default values) acc) := by
  induction keys generalizing acc with
  | nil => exact ha
  | cons i keys ih =>
      exact ih (fun j hj => hk j (by simp [hj])) (attachStep default values acc i)
        (remaining_step valid cap keys.length default values i (hk i (by simp)) acc ha)

def frameWidth (width keyCap coeffCap : Nat) : Nat := (8 * keyCap + 4 * coeffCap + 32) * width

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem rows_encoded_size {key : Ty CryptoAtom}
    (rows : List (key.Value (cryptoBase F G₁ G₂ K M) × F)) (width cap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ row ∈ rows, Q.size (rep.ty key) row.1 ≤ width) (hc : rows.length ≤ cap) :
    Q.size (rep.ty (tableTy key)) rows ≤ (4 * cap + 1) * width := by
  have hv : ∀ row ∈ rows, Q.size (rep.ty (.pair key scalar)) row ≤ 3 * width := by
    intro row hr
    have h := sizes.prod_le (rep.ty key) (rep.ty scalar) row
    have hi := hk row hr
    have hfield := hf row.2
    change Q.size (rep.ty (.pair key scalar)) row ≤ _ at h
    omega
  have h := lists.size_le_cap (rep.ty (.pair key scalar)) rows (3 * width) cap hv hc
  change Q.size (rep.ty (tableTy key)) rows ≤ _ at h
  nlinarith [Nat.mul_le_mul_left cap hh]

theorem state_encoded_size {key : Ty CryptoAtom}
    (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F)) (width cap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hn : Q.size rep.data.nat acc.1 ≤ width)
    (hk : ∀ row ∈ acc.2, Q.size (rep.ty key) row.1 ≤ width) (hc : acc.2.length ≤ cap) :
    Q.size (rep.ty (attachState key)) acc ≤ (4 * cap + 3) * width := by
  have hr := rows_encoded_size rep sizes lists acc.2 width cap hh hf hk hc
  have h := sizes.prod_le rep.data.nat (rep.ty (tableTy key)) acc
  change Q.size (rep.ty (attachState key)) acc ≤ _ at h
  nlinarith

theorem body_frame_size {key : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (i : key.Value (cryptoBase F G₁ G₂ K M))
    (acc : Nat × List (key.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : F) (keys : List (key.Value (cryptoBase F G₁ G₂ K M))) (values : List F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width keyCap coeffCap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hn : Q.size rep.data.nat acc.1 ≤ width)
    (hi : Q.size (rep.ty key) i ≤ width)
    (ha : ∀ row ∈ acc.2, Q.size (rep.ty key) row.1 ≤ width) (hac : acc.2.length ≤ keyCap)
    (hk : ∀ k ∈ keys, Q.size (rep.ty key) k ≤ width) (hkc : keys.length ≤ keyCap)
    (hvc : values.length ≤ coeffCap) (he : Q.size (rep.env Γ) env ≤ width) :
    Q.size (rep.env ([key, attachState key, scalar, .list key, .list scalar] ++ Γ))
      (i, acc, default, keys, values, env) ≤ frameWidth width keyCap coeffCap := by
  have hs := state_encoded_size rep sizes lists acc width keyCap hh hf hn ha hac
  have hkeys := lists.size_le_cap (rep.ty key) keys width keyCap hk hkc
  have hvalues := lists.size_le_cap (rep.ty scalar) values width coeffCap (fun f _ => hf f) hvc
  have hd := hf default
  have hprod := @sizes.prod_le
  have hkh := Nat.mul_le_mul_left keyCap hh
  have hvh := Nat.mul_le_mul_left coeffCap hh
  dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, attachState, tableTy,
    List.cons_append, List.nil_append, frameWidth] at *
  grind only

end Signatures.Runtime.BackendProgram.AttachCompiler
