import Signatures.Runtime.BackendSchnorrROMPass

/-! Encoding invariants for final verification and pass results. Both caches
remain visible to selection/extraction. The empty/singleton result encoding and
both replay lists are charged explicitly. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure CompletedBound (width managedCap liveCap : Nat)
    (out : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  forged : Q.size (rep.ty forgery) out.1.1 ≤ width
  challenge : Q.size (rep.ty scalar) out.1.2 ≤ 3 * width
  caches : CachesBound (Q := Q) rep width managedCap liveCap out.2

def VerifiedBound (width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (out : (NativeFork.passOutput cachePassOutput).Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  CompletedBound (Q := Q) rep width managedCap liveCap out.1 ∧
    NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap out.2

structure ResultBound (width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (out : resultTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  results : ∀ p ∈ out.1, CompletedBound (Q := Q) rep width managedCap liveCap p
  length : out.1.length ≤ 1
  tape : NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap out.2

theorem initial_reserved (width tapeWidth managedCap liveCap savedCap remainingCap initialSavedCap drawCap fuel : Nat)
    (g pk : G₁) (tape : Shared.Tape F)
    (hc : ConfigBound (Q := Q) rep width (g, pk))
    (ht : NativeUniform.StateBound (Q := Q) rep tapeWidth initialSavedCap remainingCap tape)
    (hm : fuel ≤ managedCap) (hl : fuel ≤ liveCap) (hs : initialSavedCap + fuel * drawCap ≤ savedCap) :
    NativeHandler.ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap fuel
      (((g, pk), [], []), tape) := by
  have hcache (cap : Nat) : CacheBound (Q := Q) rep width cap [] :=
    ⟨by intro p hp; simp at hp, by simp⟩
  refine ⟨⟨⟨hc, hcache managedCap, hcache liveCap⟩,
    NativeUniform.tape_mono rep tapeWidth initialSavedCap savedCap tape.1 ht.1 (by omega), ht.2⟩,
    ?_, ?_, ?_⟩
  · simpa using hm
  · simpa using hl
  · have h := ht.1.2
    dsimp only
    omega

variable [C.HasSum] [C.HasOption] {header : Nat}
  (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem completed_size (width managedCap liveCap : Nat) (hh : header ≤ width)
    (out : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (ho : CompletedBound (Q := Q) rep width managedCap liveCap out) :
    Q.size (rep.ty cachePassOutput) out ≤ (12 * (managedCap + liveCap) + 17) * width := by
  have hc := caches_size rep sizes lists width managedCap liveCap hh out.2 ho.caches
  have hp := sizes.prod_le (rep.ty observedForgery) (rep.ty cacheStore) out
  have hf := sizes.prod_le (rep.ty forgery) (rep.ty scalar) out.1
  have hforged := ho.forged
  have hchallenge := ho.challenge
  change Q.size (rep.ty cachePassOutput) out ≤ _ at hp
  change Q.size (rep.ty observedForgery) out.1 ≤ _ at hf
  nlinarith only [hc, hp, hf, hforged, hchallenge, hh]

theorem verified_size (width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth)
    (hw : (6 * (savedCap + remainingCap) + 3) * tapeWidth ≤ width)
    (out : (NativeFork.passOutput cachePassOutput).Value (cryptoBase F G₁ G₂ K M))
    (ho : VerifiedBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap out) :
    Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) out ≤
      (12 * (managedCap + liveCap) + 19) * width := by
  have hc := completed_size rep sizes lists width managedCap liveCap hh out.1 ho.1
  have htape := (NativeUniform.state_size rep sizes lists tapeWidth savedCap remainingCap ht out.2 ho.2).trans hw
  have hp := sizes.prod_le (rep.ty cachePassOutput) (rep.ty NativeUniform.stateTy) out
  change Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) out ≤ _ at hp
  nlinarith only [hc, htape, hp, hh]

theorem result_size (width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth)
    (hw : (6 * (savedCap + remainingCap) + 3) * tapeWidth ≤ width)
    (out : resultTy.Value (cryptoBase F G₁ G₂ K M))
    (ho : ResultBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap out) :
    Q.size (rep.ty resultTy) out ≤ (12 * (managedCap + liveCap) + 21) * width := by
  have hc := lists.size_le_cap (rep.ty cachePassOutput) out.1
    ((12 * (managedCap + liveCap) + 17) * width) 1
    (fun p hp => completed_size rep sizes lists width managedCap liveCap hh p (ho.results p hp)) ho.length
  have htape := (NativeUniform.state_size rep sizes lists tapeWidth savedCap remainingCap ht out.2 ho.tape).trans hw
  have hp := sizes.prod_le (rep.ty outputTy) (rep.ty NativeUniform.stateTy) out
  change Q.size (rep.ty outputTy) out.1 ≤ _ at hc
  change Q.size (rep.ty resultTy) out ≤ _ at hp
  nlinarith only [hc, htape, hp, hh]

end Signatures.Runtime.Schnorr.ListROM.NativePass
