import Proof.Rows.RowsThrC5

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.MaskStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open RowsConstruction.BaseLayout RowsConstruction.ThrCell
noncomputable section

/-! ## 1. The loop block -/

/-- The loop block's tape count (`MT` loop tapes and the two loop counters). -/
abbrev LT : Nat := MT+1+1

/-- The loop block for verdict tape `out` (`loopBank` has `out = 0^(2^s)`). -/
def loopT {q : Nat} (live : Finset (Fin q)) (s R C D : Nat) (M : Fin 254 → List Bool) (out : List Bool) :
    Fin LT → List Bool :=
  Fin.addCases (Fin.addCases (tapes live s R C D 0 0 M out) (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
    (fun _ : Fin 1 => CompareMachine.word (2^((s+1)/2)))

/-- The loop's heads for verdict length `len`. -/
def loopH (len : Nat) : Fin LT → ℕ :=
  Fin.addCases (Fin.addCases (heads len) (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 1)

/-- The verdict port of the loop block. -/
def vL : Fin LT := ⟨256, by decide⟩

theorem heads_cell (len : Nat) (c : Fin 257) : heads len (cellP c) = if c = 256 then len else 0 := by
  simp only [heads, layout_cell, PCJ45bee56da9f34d5a_VerdictFinish.heads]
  refine Fin.addCases (m := 254) (n := 3) (fun c' => ?_) (fun e => ?_) c
  · rw [Fin.addCases_left, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  · rw [Fin.addCases_right]
    fin_cases e <;> rfl

theorem tapes_cell {q : Nat} (live : Finset (Fin q)) (s R C D rN cN : Nat) (M : Fin 254 → List Bool)
    (out out' : List Bool) (c : Fin 257) (hc : c ≠ 256) :
    tapes live s R C D rN cN M out (cellP c) = tapes live s R C D rN cN M out' (cellP c) := by
  simp only [tapes, layout_cell, PCJ45bee56da9f34d5a_VerdictFinish.bank]
  by_cases hlt : c.val < 254
  · have e : c = Fin.castAdd 3 ⟨c.val, hlt⟩ := Fin.ext rfl
    rw [e, Fin.addCases_left, Fin.addCases_left]
  · have hc' : c.val ≠ 256 := fun h => hc (Fin.ext h)
    have := c.isLt
    rcases (show c.val = 254 ∨ c.val = 255 by omega) with h | h
    · have e : c = Fin.natAdd 254 (0 : Fin 3) := Fin.ext (by simp; omega)
      rw [e, Fin.addCases_right, Fin.addCases_right]
      rfl
    · have e : c = Fin.natAdd 254 (1 : Fin 3) := Fin.ext (by simp; omega)
      rw [e, Fin.addCases_right, Fin.addCases_right]
      rfl

/-- The two loop counters. -/
def k1 : Fin LT := (Fin.natAdd MT (0 : Fin 1)).castAdd 1
def k2 : Fin LT := Fin.natAdd (MT+1) (0 : Fin 1)

/-- Every loop-block port is a cell, a master, an aux port or one of the two counters. -/
theorem classify (i : Fin LT) : (∃ c : Fin 257, i = ((cellP c).castAdd 1).castAdd 1) ∨
    (∃ k : Fin 254, i = ((masterP k).castAdd 1).castAdd 1) ∨ (∃ j : Fin 7, i = ((auxP j).castAdd 1).castAdd 1) ∨
    i = k1 ∨ i = k2 := by
  have hi := i.isLt
  have hLT : LT = 520 := rfl
  by_cases h1 : i.val < 257
  · exact Or.inl ⟨⟨i.val, h1⟩, Fin.ext (by simp [cellP_val])⟩
  by_cases h2 : i.val < 511
  · exact Or.inr (Or.inl ⟨⟨i.val - 257, by omega⟩, Fin.ext (by simp [masterP_val]; omega)⟩)
  by_cases h3 : i.val < 518
  · exact Or.inr (Or.inr (Or.inl ⟨⟨i.val - 511, by omega⟩, Fin.ext (by simp [auxP_val]; omega)⟩))
  by_cases h4 : i.val = 518
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simp [k1, MT]; omega)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (by simp [k2, MT]; omega)))))

/-- Off the verdict port the loop block does not depend on the verdict tape. -/
theorem loopT_off {q : Nat} (live : Finset (Fin q)) (s R C D : Nat) (M : Fin 254 → List Bool) (out out' : List Bool)
    (i : Fin LT) (hi : i ≠ vL) : loopT live s R C D M out i = loopT live s R C D M out' i := by
  rcases classify i with ⟨c, rfl⟩ | ⟨k, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl
  · simp only [loopT, Fin.addCases_left]
    exact tapes_cell live s R C D 0 0 M out out' c (fun e => hi (by rw [e]; rfl))
  · simp [loopT, tapes]
  · simp [loopT, tapes]
  · simp [loopT, k1]
  · simp [loopT, k2]

theorem loopT_v {q : Nat} (live : Finset (Fin q)) (s R C D : Nat) (M : Fin 254 → List Bool) (out : List Bool) :
    loopT live s R C D M out vL = out := rfl

/-! ## 2. The local stage: loop block (`LT` tapes) + the two C6 words -/

/-- The local tapes: the loop block, then C6's driver `1^(2^s)` and log `0^(2·2^s+1)`. -/
def localT {q : Nat} (live : Finset (Fin q)) (s R C D : Nat) (M : Fin 254 → List Bool) (out : List Bool) :
    Fin (LT+2) → List Bool :=
  Fin.addCases (loopT live s R C D M out) (c6Words s)

def vX : Fin (LT+2) := ⟨256, by decide⟩
def d6 : Fin (LT+2) := ⟨520, by decide⟩
def g6 : Fin (LT+2) := ⟨521, by decide⟩

def hot (i : Fin (LT+2)) : Prop := i.val = 517 ∨ i.val = 518 ∨ i.val = 519

instance (i : Fin (LT+2)) : Decidable (hot i) := by unfold hot; infer_instance

def moveIn : Machine (LT+2) 2 := DecompositionCountPosition.move (fun i => if hot i then HeadMove.right else HeadMove.stay)
def moveOut : Machine (LT+2) 2 := DecompositionCountPosition.move (fun i => if hot i then HeadMove.left else HeadMove.stay)
def rwM : Machine (LT+2) 3 := RecoveryFocus.machine ![vX, d6, g6] CompetitorRecordRewind.machine

/-- **The mask stage** for a loop machine `M` (one fixed machine per `M`). -/
def maskStage {sM : Nat} (M : Machine LT sM) :=
  Composition.machine moveIn (Composition.machine (TapeEmbedding.machine 2 M) (Composition.machine moveOut rwM))

def inH (i : Fin (LT+2)) : ℕ := if hot i then 1 else 0

/-- Every local port: a loop-block port (classified) or one of the two C6 words. -/
theorem classify2 (i : Fin (LT+2)) : (∃ c : Fin 257, i = (((cellP c).castAdd 1).castAdd 1).castAdd 2) ∨
    (∃ k : Fin 254, i = (((masterP k).castAdd 1).castAdd 1).castAdd 2) ∨
    (∃ j : Fin 7, i = (((auxP j).castAdd 1).castAdd 1).castAdd 2) ∨
    i = k1.castAdd 2 ∨ i = k2.castAdd 2 ∨ i = Fin.natAdd LT (0 : Fin 2) ∨ i = Fin.natAdd LT (1 : Fin 2) := by
  have hi := i.isLt
  have hLT : LT = 520 := rfl
  by_cases h0 : i.val < LT
  · rcases classify ⟨i.val, h0⟩ with ⟨c, hc⟩ | ⟨k, hk⟩ | ⟨j, hj⟩ | h | h
    · exact Or.inl ⟨c, Fin.ext (by have := congrArg Fin.val hc; simpa using this)⟩
    · exact Or.inr (Or.inl ⟨k, Fin.ext (by have := congrArg Fin.val hk; simpa using this)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, Fin.ext (by have := congrArg Fin.val hj; simpa using this)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by have := congrArg Fin.val h; simpa using this)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by have := congrArg Fin.val h; simpa using this))))))
  · by_cases h1 : i.val = 520
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simp; omega)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (by simp; omega)))))))

theorem inH_eq : inH = Fin.addCases (loopH 0) (fun _ : Fin 2 => 0) := by
  funext i
  rcases classify2 i with ⟨c, rfl⟩ | ⟨k, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl | rfl | rfl
  · simp only [loopH, Fin.addCases_left]
    rw [heads_cell]
    unfold inH hot
    rw [if_neg (by simp [cellP_val]; omega)]
    split <;> rfl
  · simp only [loopH, Fin.addCases_left]
    unfold inH hot
    rw [if_neg (by simp [masterP_val]; omega)]
    simp [heads]
  · simp only [loopH, Fin.addCases_left, heads, layout_aux, auxHeads]
    unfold inH hot
    fin_cases j <;> simp [auxP_val]
  · rw [Fin.addCases_left]
    simp only [loopH, k1, Fin.addCases_left, Fin.addCases_right]
    unfold inH hot
    rw [if_pos (by simp [MT])]
  · rw [Fin.addCases_left]
    simp only [loopH, k2, Fin.addCases_right]
    unfold inH hot
    rw [if_pos (by simp [MT])]
  · rw [Fin.addCases_right]
    unfold inH hot
    rw [if_neg (by simp [LT, MT])]
  · rw [Fin.addCases_right]
    unfold inH hot
    rw [if_neg (by simp [LT, MT])]

theorem move_in (A : Fin (LT+2) → List Bool) : Step moveIn 1 (fun _ => 0) A inH A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run
    (fun i : Fin (LT+2) => if hot i then HeadMove.right else HeadMove.stay) (fun _ => 0) A
  refine Step.of_run hr ?_ (by rw [hf])
  rw [hf]
  funext i
  show (if hot i then HeadMove.right else HeadMove.stay).apply 0 = inH i
  unfold inH
  split <;> rfl

/-- The heads after the loop (verdict head at `len`, the three hot heads at `1`). -/
def midH (len : Nat) (i : Fin (LT+2)) : ℕ := if i = vX then len else inH i

theorem midH_eq (len : Nat) : Fin.addCases (loopH len) (fun _ : Fin 2 => 0) = midH len := by
  funext i
  rw [midH, inH_eq]
  by_cases hv : i = vX
  · subst hv
    rw [if_pos rfl]
    rfl
  · rw [if_neg hv]
    dsimp only
    rcases classify2 i with ⟨c, rfl⟩ | ⟨k, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl | rfl | rfl
    · simp only [loopH, Fin.addCases_left]
      rw [heads_cell, heads_cell]
      have hc : c ≠ 256 := fun e => hv (by rw [e]; rfl)
      rw [if_neg hc, if_neg hc]
    · simp [loopH, heads]
    · simp [loopH, heads]
    · rw [Fin.addCases_left, Fin.addCases_left]
      simp only [loopH, k1, Fin.addCases_left, Fin.addCases_right]
    · rw [Fin.addCases_left, Fin.addCases_left]
      simp only [loopH, k2, Fin.addCases_right]
    · rw [Fin.addCases_right, Fin.addCases_right]
    · rw [Fin.addCases_right, Fin.addCases_right]

def outH (len : Nat) (i : Fin (LT+2)) : ℕ := if i = vX then len else 0

theorem move_out (len : Nat) (A : Fin (LT+2) → List Bool) : Step moveOut 1 (midH len) A (outH len) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run
    (fun i : Fin (LT+2) => if hot i then HeadMove.left else HeadMove.stay) (midH len) A
  refine Step.of_run hr ?_ (by rw [hf])
  rw [hf]
  funext i
  show (if hot i then HeadMove.left else HeadMove.stay).apply (midH len i) = outH len i
  unfold midH outH inH
  by_cases hv : i = vX
  · subst hv
    have : ¬ hot vX := by simp [hot, vX]
    rw [if_neg this, if_pos rfl, if_pos rfl]
    rfl
  · rw [if_neg hv, if_neg hv]
    split <;> rfl

theorem rewind_pad (source : List Bool) (C pos Lg : Nat) (hp : pos ≤ C) (hL : C ≤ Lg) :
    Step CompetitorRecordRewind.machine (2*C+2) ![pos,0,0]
      ![source, List.replicate C true, List.replicate Lg false]
      ![0,0,0] ![source, List.replicate C true, List.replicate Lg false] := by
  obtain ⟨r, hr, hf, hs⟩ := CompetitorRecordRewind.rewind_run source C pos hp
  have core : Step CompetitorRecordRewind.machine (2*C+2) ![pos,0,0]
      ![source, List.replicate C true, []] ![0,0,0]
      ![source, List.replicate C true, List.replicate C false] :=
    ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, hs.le⟩
  have run := core.pad ![0,0,Lg]
  have hi : (fun i => ZeroPadding.pad (![0,0,Lg] i) (![source, List.replicate C true, []] i)) =
      ![source, List.replicate C true, List.replicate Lg false] := by
    funext i; fin_cases i <;> simp [ZeroPadding.pad]
  have ho : (fun i => ZeroPadding.pad (![0,0,Lg] i) (![source, List.replicate C true, List.replicate C false] i)) =
      ![source, List.replicate C true, List.replicate Lg false] := by
    funext i; fin_cases i <;> simp [ZeroPadding.pad]
    omega
  rw [hi, ho] at run
  exact run

theorem pad_len (n : Nat) (w : List Bool) (h : w.length = n) : ZeroPadding.pad n w = w := by
  simp [ZeroPadding.pad, h]

/-- **The mask stage.** For any loop machine `M` whose run appends a word `w` of length `2^s` to an empty verdict tape
(the `thr_row_mask`/`sym_row_mask` shape), the fixed `maskStage M` runs from the row's loop block (verdict `0^(2^s)`) and
C6 words, all heads `0`, to the same block with the verdict tape `w`, all heads `0`. -/
theorem mask_step {q : Nat} (live : Finset (Fin q)) (s R C D : Nat) (Ms : Fin 254 → List Bool) (w : List Bool)
    (hw : w.length = 2^s) {sM : Nat} (M : Machine LT sM) (n : Nat)
    (hM : Step M n (loopH 0) (loopT live s R C D Ms []) (loopH w.length) (loopT live s R C D Ms w)) :
    Step (maskStage M) (1+1+(n+1+(1+1+(2*2^s+2)))) (fun _ => 0)
      (localT live s R C D Ms (List.replicate (2^s) false)) (fun _ => 0) (localT live s R C D Ms w) := by
  -- the padded loop
  have hp := hM.pad (fun i => if i = vL then 2^s else 0)
  have ein : (fun i => ZeroPadding.pad (if i = vL then 2^s else 0) (loopT live s R C D Ms [] i)) =
      loopT live s R C D Ms (List.replicate (2^s) false) := by
    funext i
    by_cases hi : i = vL
    · subst hi; rw [if_pos rfl, loopT_v, loopT_v]; simp [ZeroPadding.pad]
    · rw [if_neg hi, ZeroPadding.pad_zero, loopT_off live s R C D Ms [] _ i hi]
  have eout : (fun i => ZeroPadding.pad (if i = vL then 2^s else 0) (loopT live s R C D Ms w i)) =
      loopT live s R C D Ms w := by
    funext i
    by_cases hi : i = vL
    · subst hi; rw [if_pos rfl, loopT_v, pad_len _ _ hw]
    · rw [if_neg hi, ZeroPadding.pad_zero]
  rw [ein, eout] at hp
  have s2 := hp.embed (fun _ : Fin 2 => 0) (c6Words s)
  rw [← inH_eq, midH_eq] at s2
  have s1 := move_in (localT live s R C D Ms (List.replicate (2^s) false))
  have s3 := move_out w.length (localT live s R C D Ms w)
  -- the rewind
  have hslots : Function.Injective (![vX, d6, g6] : Fin 3 → Fin (LT+2)) := by decide
  have rw0 := rewind_pad (localT live s R C D Ms w vX) (2^s) w.length (2*2^s+1) (by omega) (by omega)
  have s4 := SymVerdict.focus_at rw0 ![vX, d6, g6] hslots (outH w.length) (localT live s R C D Ms w)
    (fun j => by fin_cases j <;> simp [outH, vX, d6, g6])
    (fun j => by fin_cases j <;> rfl)
  have hH : dockH ![vX, d6, g6] (outH w.length) ![0,0,0] = fun _ => 0 := by
    funext i
    by_cases hx : ∃ j, (![vX, d6, g6] : Fin 3 → Fin (LT+2)) j = i
    · obtain ⟨j, rfl⟩ := hx
      rw [dockH_slot _ hslots]
      fin_cases j <;> rfl
    · rw [dockH_other _ _ _ _ (fun j he => hx ⟨j, he⟩)]
      unfold outH
      rw [if_neg (fun he => hx ⟨0, he.symm⟩)]
  have hA : install ![vX, d6, g6] (localT live s R C D Ms w)
      ![localT live s R C D Ms w vX, List.replicate (2^s) true, List.replicate (2*2^s+1) false] =
      localT live s R C D Ms w := by
    apply install_existing
    intro j
    fin_cases j <;> rfl
  rw [hH, hA] at s4
  exact s1.seq (s2.seq (s3.seq s4))

end
end RowsConstruction.MaskStage
