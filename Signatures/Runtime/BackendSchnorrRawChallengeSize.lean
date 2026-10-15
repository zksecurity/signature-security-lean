import Signatures.Runtime.BackendSchnorrRawChallenge
import Signatures.Runtime.BackendSchnorrRawUniformSize

/-! Native challenge encoding bounds share the same saved/remaining tape
invariants as private draws. Both lists are counted separately. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeChallenge

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def Output (width savedCap remainingCap : Nat)
    (out : drawTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size (rep.ty scalar) out.1 ≤ width ∧
    NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap out.2

theorem prepare_property [Zero F] (width savedCap remainingCap : Nat)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap state) :
    Output (Q := Q) rep width savedCap remainingCap (prepareValue state).2 := by
  have fieldWidth : Q.size (rep.ty scalar) (SeedTape.pop 1 (0, (0 : F), 0) state.2).2.1.2.1 ≤ width := by
    rcases SeedTape.pop_answer_mem_or_default 1 (0, (0 : F), 0) state.2 with member | same
    · exact (bound.2.1 _ member).2.1
    · simpa only [same] using hz
  have rest := (NativeUniform.pop_property rep width remainingCap 1 (0, (0 : F), 0) state.2 bound.2).1
  cases found : (SeedTape.pop 1 (0, (0 : F), 0) state.2).1 with
  | true => simpa [Output, prepareValue, found, NativeUniform.StateBound] using
      And.intro fieldWidth (And.intro bound.1 rest)
  | false => simpa [Output, prepareValue, found, NativeUniform.StateBound] using
      And.intro fieldWidth bound

theorem save_property (width savedCap remainingCap : Nat)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : Output (Q := Q) rep width savedCap remainingCap input) :
    Output (Q := Q) rep width (savedCap + 1) remainingCap (saveValue input) := by
  refine ⟨bound.1, ⟨?_, ?_⟩, bound.2.2⟩
  · intro cell member
    rcases List.mem_append.mp member with old | fresh
    · exact bound.2.1.1 cell old
    · have same : cell = (1, input.1, 0) := by simpa using fresh
      subst cell
      exact ⟨hn1, bound.1, hn0⟩
  · change (input.2.1 ++ [(1, input.1, 0)]).length ≤ savedCap + 1
    simp only [List.length_append, List.length_singleton]
    exact Nat.add_le_add_right bound.2.1.2 1

section Size

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem output_size (width savedCap remainingCap : Nat) (hh : header ≤ width)
    (out : drawTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : Output (Q := Q) rep width savedCap remainingCap out) :
    Q.size (rep.ty drawTy) out ≤ (6 * (savedCap + remainingCap) + 5) * width := by
  have hs := NativeUniform.state_size rep sizes lists width savedCap remainingCap hh out.2 bound.2
  have hp := sizes.prod_le (rep.ty scalar) (rep.ty stateTy) out
  have hf := bound.1
  change Q.size (rep.ty drawTy) out ≤ _ at hp
  nlinarith

theorem prepare_size [Zero F] (width savedCap remainingCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap state) :
    Q.size (rep.ty prepareTy) (prepareValue state) ≤ (6 * (savedCap + remainingCap) + 7) * width := by
  have hs := output_size rep sizes lists width savedCap remainingCap hh (prepareValue state).2
    (prepare_property rep width savedCap remainingCap hz state bound)
  have hp := sizes.prod_le rep.data.bool (rep.ty drawTy) (prepareValue state)
  have hb' := hb (prepareValue state).1
  change Q.size (rep.ty prepareTy) (prepareValue state) ≤ _ at hp
  nlinarith

end Size

end Signatures.Runtime.Schnorr.RawTape.NativeChallenge
