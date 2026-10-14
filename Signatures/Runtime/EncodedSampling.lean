import Signatures.Runtime.SamplingState
import VCVio.OracleComp.Constructions.Replicate

/-! Sampling into an encoded list using first-order codecs. The ambient store
is untouched; each primitive draw, codec, list cell and loop step is charged. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {a cell : Ty Atom} {I S : Type} {spec : OracleSpec I}

def encodedCons (draw : Cmd .unit a) (encode : Expr Op [a] cell) :
    Program Op Cmd [.list cell, .nat] (.list cell) :=
  .bind (.query draw .unit)
    (.bind (.call (.ret encode) (.cons (.var .here) .nil))
      (.ret (.cons (.var .here) (.var (.there (.there .here))))))

def encodedList (draw : Cmd .unit a) (encode : Expr Op [a] cell) :
    Program Op Cmd [.nat] (.list cell) :=
  .loop (.var .here) .nil (encodedCons draw encode)

def encodedTable (draw : Cmd .unit a) (encode : Expr Op [a] cell) :
    Program Op Cmd [.nat] (.list cell) :=
  .bind (encodedList draw encode) (.ret reverseList)

def encodedStep (P : Primitives base Op) (encode : Expr Op [a] cell)
    (random : OracleComp spec (a.Value base)) (price : Nat) (xs : List (cell.Value base)) :
    OracleComp spec (Run (List (cell.Value base))) :=
  (fun x => let r := encode.run P (x, ()); ⟨r.value :: xs, price + r.steps + 16⟩) <$> random

theorem encodedCons_run (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S (OracleComp spec))) (draw : Cmd .unit a)
    (encode : Expr Op [a] cell) (random : OracleComp spec (a.Value base)) (price : Nat)
    (hdraw : ∀ s, (H draw ()).run s = (fun x => (⟨x, price⟩, s)) <$> random)
    (xs : List (cell.Value base)) (n : Nat) (s : S) :
    ((encodedCons draw encode).run P H (xs, n, ())).run s =
      (fun r => (r, s)) <$> encodedStep P encode random price xs := by
  simp only [encodedCons, Program.run, Args.run, Expr.run, Var.get, Var.depth,
    hdraw, encodedStep, Functor.map_map, bind_pure_comp, StateT.run_map, map_pure]
  congr 1
  funext x
  congr 2
  omega

theorem encodedList_run (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S (OracleComp spec))) (draw : Cmd .unit a)
    (encode : Expr Op [a] cell) (random : OracleComp spec (a.Value base)) (price : Nat)
    (hdraw : ∀ s, (H draw ()).run s = (fun x => (⟨x, price⟩, s)) <$> random)
    (n : Nat) (s : S) :
    ((encodedList draw encode).run P H (n, ())).run s =
      (fun r => (⟨r.value, r.steps + 3⟩, s)) <$>
        repeatRun (encodedStep P encode random price) n [] := by
  have h := repeatRun_run_state (encodedStep P encode random price)
    (fun xs => (encodedCons draw encode).run P H (xs, n, ()))
    (fun xs s => encodedCons_run P H draw encode random price hdraw xs n s) n [] s
  simp [encodedList, Program.run, Expr.run, Var.get, Var.depth, h,
    bind_pure_comp, Nat.add_comm, Nat.add_left_comm]

theorem encodedTable_run (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S (OracleComp spec))) (draw : Cmd .unit a)
    (encode : Expr Op [a] cell) (random : OracleComp spec (a.Value base)) (price : Nat)
    (hdraw : ∀ s, (H draw ()).run s = (fun x => (⟨x, price⟩, s)) <$> random)
    (n : Nat) (s : S) :
    ((encodedTable draw encode).run P H (n, ())).run s =
      (fun r => (⟨r.value.reverse,
        r.steps + ((reverseList (Γ := [.nat])).run P (r.value, n, ())).steps + 5⟩, s)) <$>
        repeatRun (encodedStep P encode random price) n [] := by
  simp only [encodedTable, Program.run, StateT.run_bind, StateT.run_pure,
    encodedList_run P H draw encode random price hdraw n s, bind_map_left]
  simp only [bind_pure_comp, Expr.run_value, map_pure,
    reverseList_denote (cell := cell) (Γ := [.nat]) P]
  congr 1
  funext r
  congr 2
  omega

theorem repeatDenote_encode {A B : Type} (random : OracleComp spec A) (encode : A → B)
    (n : Nat) (xs : List B) :
    repeatDenote (fun ys => (fun x => encode x :: ys) <$> random) n xs =
      (fun ys => (ys.map encode).reverse ++ xs) <$> replicate n random := by
  induction n generalizing xs with
  | zero => simp [repeatDenote]
  | succ n ih =>
      simp [repeatDenote, ih, bind_map_left, map_bind, Functor.map_map, List.reverse_cons,
        List.append_assoc]

theorem encodedLoop_erase (P : Primitives base Op) (encode : Expr Op [a] cell)
    (random : OracleComp spec (a.Value base)) (price n : Nat) :
    Run.value <$> repeatRun (encodedStep P encode random price) n [] =
      (fun xs => (xs.map (fun x => encode.denote P (x, ()))).reverse) <$> replicate n random := by
  rw [repeatRun_erase]
  simpa only [encodedStep, Functor.map_map, Expr.run_value, List.append_nil] using
    repeatDenote_encode random (fun x => encode.denote P (x, ())) n []

theorem encodedTable_erase (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S (OracleComp spec))) (draw : Cmd .unit a)
    (encode : Expr Op [a] cell) (random : OracleComp spec (a.Value base)) (price : Nat)
    (hdraw : ∀ s, (H draw ()).run s = (fun x => (⟨x, price⟩, s)) <$> random)
    (n : Nat) (s : S) :
    (fun p => (p.1.value, p.2)) <$> ((encodedTable draw encode).run P H (n, ())).run s =
      (fun xs => (xs.map (fun x => encode.denote P (x, ())), s)) <$> replicate n random := by
  rw [encodedTable_run P H draw encode random price hdraw]
  have h := congrArg (Functor.map (fun xs => (xs.reverse, s)))
    (encodedLoop_erase P encode random price n)
  simpa only [Functor.map_map, List.reverse_reverse] using h

theorem encodedTable_bound (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S (OracleComp spec))) (draw : Cmd .unit a)
    (encode : Expr Op [a] cell) (random : OracleComp spec (a.Value base)) (price cEncode : Nat)
    (hdraw : ∀ s, (H draw ()).run s = (fun x => (⟨x, price⟩, s)) <$> random)
    (hencode : ∀ x, (encode.run P (x, ())).steps ≤ cEncode)
    (n : Nat) (s : S) (out : Run (List (cell.Value base)) × S)
    (hout : out ∈ support (((encodedTable draw encode).run P H (n, ())).run s)) :
    out.1.steps ≤ n * (price + cEncode + 25) + 10 ∧ out.1.value.length = n ∧ out.2 = s := by
  rw [encodedTable_run P H draw encode random price hdraw] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hstep : ∀ xs z, z ∈ support (encodedStep P encode random price xs) →
      z.steps ≤ price + cEncode + 16 := by
    intro xs z hz
    simp only [encodedStep, support_map, Set.mem_image] at hz
    obtain ⟨x, _, rfl⟩ := hz
    have := hencode x
    dsimp; omega
  have hb := repeatRun_steps_le (encodedStep P encode random price)
    (price + cEncode + 16) hstep n [] r hr
  have hv : r.value ∈ support ((fun xs =>
      (xs.map (fun x => encode.denote P (x, ()))).reverse) <$> replicate n random) := by
    rw [← encodedLoop_erase, support_map]
    exact ⟨r, hr, rfl⟩
  simp only [support_map, Set.mem_image, support_replicate, Set.mem_ofPred_eq] at hv
  obtain ⟨xs, ⟨hxs, _⟩, he⟩ := hv
  have hl : r.value.length = n := by rw [← he]; simpa using hxs
  have hrb := reverseList_steps_le (cell := cell) (Γ := [.nat]) P r.value (n, ())
  refine ⟨?_, by simpa using hl, rfl⟩
  dsimp
  rw [hl] at hrb
  nlinarith

/-- Concatenation copies the first list's spine and preserves the second tail. -/
def appendCode : Expr Op [.list cell, .list cell] (.list cell) :=
  .letE reverseList (.fold (.var .here) (.var (.there (.there .here)))
    (.cons (.var .here) (.var (.there .here))))

theorem appendCode_denote (P : Primitives base Op) (xs ys : List (cell.Value base)) :
    appendCode.denote P (xs, ys, ()) = xs ++ ys := by
  simp only [appendCode, Expr.denote, Var.get]
  rw [reverseList_denote]
  simp [← Function.flip_def]

theorem appendCode_steps (P : Primitives base Op) (xs ys : List (cell.Value base)) :
    (appendCode.run P (xs, ys, ())).steps ≤ 14 * xs.length + 12 := by
  have hr := reverseList_steps_le (cell := cell) (Γ := [.list cell]) P xs (ys, ())
  have hf := foldRun_steps_le
    (fun (x : cell.Value base) (acc : List (cell.Value base)) =>
      (Expr.cons (.var .here) (.var (.there .here)) : Expr Op
        [cell, .list cell, .list cell, .list cell, .list cell] (.list cell)).run P
          (x, acc, xs.reverse, xs, ys, ())) 4
    (by intros; simp [Expr.run, Var.get, Var.depth]) xs.reverse ys
  dsimp only [appendCode, Expr.run, Var.get, Var.depth]
  simp only [Expr.run_value]
  rw [reverseList_denote]
  simp only [List.length_reverse] at hf
  dsimp [Expr.run, Var.get, Var.depth] at hf
  nlinarith

end Signatures.Runtime
