import Proof.CaseAnalysis.RowsTupleSeekFrame

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceResident
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## The masked reset from zero heads, with the log's length bounded -/

theorem mask0 {t s : ℕ} {p : Machine t s} {n : ℕ} {hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin hout tout) :
    ∃ k, k ≤ n ∧ Step (MaskedReset.machine p (fun _ => true)) (2 * n + 2)
      (Fin.addCases (fun _ : Fin t => (0 : ℕ)) (fun _ : Fin 1 => 0))
      (Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool)))
      (Fin.addCases (fun _ : Fin t => (0 : ℕ)) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate k false)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hhead : ∀ i, (fun _ : Fin t => true) i = true → r.final.heads i ≤ r.steps := by
    intro i _
    have h := SelectiveReset.prefix_head (prefix_of_run p n _ r hr).1 i
    have h0 : (⟨p.start, (fun _ => 0), tin⟩ : Configuration t s).heads i = 0 := rfl
    omega
  obtain ⟨result, hres, hfinal, hsteps, _⟩ := MaskedReset.reset_run p (fun _ => true) n _ r hr hhead
  have hentry : Rewind.recording (⟨p.start, (fun _ => 0), tin⟩ : Configuration t s) 0 =
      (⟨(MaskedReset.machine p (fun _ => true)).start, Fin.addCases (fun _ : Fin t => (0 : ℕ)) (fun _ : Fin 1 => 0),
        Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool))⟩ : Configuration (t+1) (s+2)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp only [Rewind.recording, Rewind.config, Fin.addCases_left]
      · have hj : j = 0 := Fin.eq_zero j
        subst hj
        simp only [Rewind.recording, Rewind.config, Fin.addCases_right, List.replicate_zero]
  rw [hentry] at hres
  have hfuel : 2 * r.steps + 2 ≤ 2 * n + 2 := by omega
  have hmore := runFrom_moreFuel (MaskedReset.machine p (fun _ => true)) (2 * r.steps + 2)
    (2 * n + 2 - (2 * r.steps + 2)) _ result hres
  rw [Nat.add_sub_of_le hfuel] at hmore
  refine ⟨r.steps, by omega, result, hmore, ?_, ?_, by omega⟩
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, if_true]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, ht]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]

/-! ## One framed copy, rewound -/

/-- The rewound framed-word copier: tape 0 the source, tape 1 the copy, tape 2 the reset log. -/
def copyM := MaskedReset.machine (CloseoutRowsTupleSeek.frameMachine true) (fun _ => true)

/-- The local bank of the copier. -/
def cBank (src out log : List Bool) : Fin (2 + 1) → List Bool :=
  Fin.addCases (CloseoutRowsTupleSeek.fieldData src out) (fun _ : Fin 1 => log)


/-- **The copy**: `frame w ++ tail` stays, `frame w` is written on the empty copy tape, every head back at `0`. -/
theorem copy_run (w tail : List Bool) : ∃ k, k ≤ 2 * w.length + 1 ∧
    Step copyM (2 * (2 * w.length + 1) + 2) (fun _ => 0) (cBank (frame w ++ tail) [] []) (fun _ => 0)
      (cBank (frame w ++ tail) (frame w) (List.replicate k false)) := by
  have h := CloseoutRowsTupleSeek.frame_run true [] w tail []
  simp only [List.nil_append, List.length_nil, CloseoutRowsTupleSeek.selected, if_true] at h
  have h0 : CloseoutRowsTupleSeek.fieldHeads 0 ([] : List Bool) = fun _ => 0 := by
    funext i; fin_cases i <;> rfl
  rw [h0] at h
  obtain ⟨k, hk, st⟩ := mask0 h
  have eH : Fin.addCases (fun _ : Fin 2 => (0 : ℕ)) (fun _ : Fin 1 => 0) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [eH] at st
  exact ⟨k, hk, st⟩

/-- The padding of the three copier tapes. -/
def cCap (R : ℕ) : Fin (2 + 1) → ℕ := Fin.addCases (fun j : Fin 2 => if j.val = 0 then 0 else R) (fun _ : Fin 1 => R)

theorem pad_repl (R k : ℕ) (hk : k ≤ R) : ZeroPadding.pad R (List.replicate k false) = List.replicate R false := by
  simp only [ZeroPadding.pad, List.length_replicate, ← List.replicate_add]
  congr 1
  omega

/-- **One copy in any ambient bank**: source `s` holds `pad Q (frame w)`, target `t` and log `g` are `R`-blank, heads `0`
there; afterwards exactly the target changed, to `pad R (frame w)`, and every head is where it was. -/
theorem copy_step {u : ℕ} (s t g : Fin u) (hst : s ≠ t) (hsg : s ≠ g) (htg : t ≠ g)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (w : List Bool) (Q R : ℕ)
    (hHs : H s = 0) (hHt : H t = 0) (hHg : H g = 0)
    (hs : A s = ZeroPadding.pad Q (frame w)) (ht : A t = List.replicate R false) (hg : A g = List.replicate R false)
    (hR : 2 * w.length + 1 ≤ R) :
    Step (RecoveryFocus.machine ![s, t, g] copyM) (2 * (2 * w.length + 1) + 2) H A H
      (Function.update A t (ZeroPadding.pad R (frame w))) := by
  have hinj : Function.Injective (![s, t, g] : Fin 3 → Fin u) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  obtain ⟨k, hk, st⟩ := copy_run w (List.replicate (Q - (frame w).length) false)
  have sp := st.pad (cCap R)
  have sf := sp.focus ![s, t, g] hinj H A
  have eH : dockH ![s, t, g] H (fun _ => 0) = H := by
    funext x
    by_cases hx : ∃ j, (![s, t, g] : Fin 3 → Fin u) j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [dockH_slot _ hinj]
      fin_cases j
      · exact hHs.symm
      · exact hHt.symm
      · exact hHg.symm
    · simp only [not_exists] at hx
      exact dockH_other _ _ _ _ hx
  have eIn : install ![s, t, g] A (fun i => ZeroPadding.pad (cCap R i)
      (cBank (frame w ++ List.replicate (Q - (frame w).length) false) [] [] i)) = A := by
    apply install_existing
    intro j
    fin_cases j
    · show A s = ZeroPadding.pad 0 (frame w ++ List.replicate (Q - (frame w).length) false)
      rw [ZeroPadding.pad_zero, hs]
      rfl
    · show A t = ZeroPadding.pad R []
      rw [ht]
      exact (pad_repl R 0 (Nat.zero_le _)).symm
    · show A g = ZeroPadding.pad R []
      rw [hg]
      exact (pad_repl R 0 (Nat.zero_le _)).symm
  have eOut : install ![s, t, g] A (fun i => ZeroPadding.pad (cCap R i)
      (cBank (frame w ++ List.replicate (Q - (frame w).length) false) (frame w) (List.replicate k false) i)) =
      Function.update A t (ZeroPadding.pad R (frame w)) := by
    funext x
    by_cases hx : ∃ j, (![s, t, g] : Fin 3 → Fin u) j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [install_slot _ hinj]
      fin_cases j
      · show ZeroPadding.pad 0 (frame w ++ List.replicate (Q - (frame w).length) false) = Function.update A t _ s
        rw [Function.update_of_ne hst, ZeroPadding.pad_zero, hs]
        rfl
      · show ZeroPadding.pad R (frame w) = Function.update A t _ t
        rw [Function.update_self]
      · show ZeroPadding.pad R (List.replicate k false) = Function.update A t _ g
        rw [Function.update_of_ne (Ne.symm htg), hg, pad_repl R k (by omega)]
    · simp only [not_exists] at hx
      rw [install_other _ _ _ _ hx, Function.update_of_ne (show x ≠ t from fun e => hx 1 (by rw [e]; rfl))]
  rw [eH, eIn, eOut] at sf
  exact sf

/-- Which source feeds target `5 + i`: native, support, support, TOP, `1^q`, `1^q`, `1^K`. -/
def srcIx : Fin 7 → Fin 5 := ![0, 1, 1, 2, 3, 3, 4]

/-- Source port of copy `i`. -/
def srcP (i : Fin 7) : Fin 13 := ⟨(srcIx i).val, by have := (srcIx i).isLt; omega⟩
/-- Target port of copy `i`. -/
def tgtP (i : Fin 7) : Fin 13 := ⟨5 + i.val, by omega⟩
/-- The shared reset log. -/
def logP : Fin 13 := ⟨12, by omega⟩

/-- Copy `i`, docked on its source, target and the log. -/
def cM (i : Fin 7) := RecoveryFocus.machine ![srcP i, tgtP i, logP] copyM

/-- **The copies stage** (one fixed machine). -/
def copiesM :=
  Composition.machine (cM ⟨0, by omega⟩) (Composition.machine (cM ⟨1, by omega⟩)
    (Composition.machine (cM ⟨2, by omega⟩) (Composition.machine (cM ⟨3, by omega⟩)
      (Composition.machine (cM ⟨4, by omega⟩) (Composition.machine (cM ⟨5, by omega⟩) (cM ⟨6, by omega⟩))))))

/-- Cost of copy `i`. -/
def cc (w : Fin 5 → List Bool) (i : Fin 7) : ℕ := 2 * (2 * (w (srcIx i)).length + 1) + 2

/-- Cost of the stage (`R`-free: linear in the five words' lengths). -/
def copiesCost (w : Fin 5 → List Bool) : ℕ :=
  cc w ⟨0, by omega⟩ + 1 + (cc w ⟨1, by omega⟩ + 1 + (cc w ⟨2, by omega⟩ + 1 + (cc w ⟨3, by omega⟩ + 1 +
    (cc w ⟨4, by omega⟩ + 1 + (cc w ⟨5, by omega⟩ + 1 + cc w ⟨6, by omega⟩)))))

/-- The local bank after the first `i` copies. -/
def bankAt (w : Fin 5 → List Bool) (R : ℕ) (B : Fin 13 → List Bool) (i : ℕ) (x : Fin 13) : List Bool :=
  if h : 5 ≤ x.val ∧ x.val < 5 + i ∧ x.val < 12 then
    ZeroPadding.pad R (frame (w (srcIx ⟨x.val - 5, by omega⟩)))
  else B x

theorem bankAt_zero (w : Fin 5 → List Bool) (R : ℕ) (B : Fin 13 → List Bool) : bankAt w R B 0 = B := by
  funext x
  unfold bankAt
  rw [dif_neg (by omega)]

theorem stepAt (w : Fin 5 → List Bool) (Q : Fin 5 → ℕ) (R : ℕ) (B : Fin 13 → List Bool)
    (hsrc : ∀ i : Fin 5, B ⟨i.val, by omega⟩ = ZeroPadding.pad (Q i) (frame (w i)))
    (hblank : ∀ j : Fin 13, 5 ≤ j.val → B j = List.replicate R false)
    (hR : ∀ i, 2 * (w i).length + 1 ≤ R) (i : ℕ) (hi : i < 7) :
    Step (cM ⟨i, hi⟩) (cc w ⟨i, hi⟩) (fun _ => 0) (bankAt w R B i) (fun _ => 0) (bankAt w R B (i + 1)) := by
  have hsv : (srcP ⟨i, hi⟩).val < 5 := (srcIx ⟨i, hi⟩).isLt
  have htv : (tgtP ⟨i, hi⟩).val = 5 + i := rfl
  have hlv : logP.val = 12 := rfl
  have h1 : srcP ⟨i, hi⟩ ≠ tgtP ⟨i, hi⟩ := fun e => by have := congrArg Fin.val e; omega
  have h2 : srcP ⟨i, hi⟩ ≠ logP := fun e => by have := congrArg Fin.val e; omega
  have h3 : tgtP ⟨i, hi⟩ ≠ logP := fun e => by have := congrArg Fin.val e; omega
  have hs : bankAt w R B i (srcP ⟨i, hi⟩) = ZeroPadding.pad (Q (srcIx ⟨i, hi⟩)) (frame (w (srcIx ⟨i, hi⟩))) := by
    unfold bankAt
    rw [dif_neg (by omega)]
    exact hsrc (srcIx ⟨i, hi⟩)
  have ht : bankAt w R B i (tgtP ⟨i, hi⟩) = List.replicate R false := by
    unfold bankAt
    rw [dif_neg (by omega)]
    exact hblank _ (by omega)
  have hg : bankAt w R B i logP = List.replicate R false := by
    unfold bankAt
    rw [dif_neg (by omega)]
    exact hblank _ (by omega)
  have st := copy_step (srcP ⟨i, hi⟩) (tgtP ⟨i, hi⟩) logP h1 h2 h3 (fun _ => 0) (bankAt w R B i)
    (w (srcIx ⟨i, hi⟩)) (Q (srcIx ⟨i, hi⟩)) R rfl rfl rfl hs ht hg (hR _)
  have e : Function.update (bankAt w R B i) (tgtP ⟨i, hi⟩) (ZeroPadding.pad R (frame (w (srcIx ⟨i, hi⟩)))) =
      bankAt w R B (i + 1) := by
    funext x
    by_cases hx : x = tgtP ⟨i, hi⟩
    · subst hx
      rw [Function.update_self]
      unfold bankAt
      rw [dif_pos (by omega)]
      congr 4
      exact Fin.ext (by simp [tgtP])
    · rw [Function.update_of_ne hx]
      have hxv : x.val ≠ 5 + i := fun e => hx (Fin.ext (by rw [htv]; exact e))
      unfold bankAt
      by_cases c : 5 ≤ x.val ∧ x.val < 5 + i ∧ x.val < 12
      · rw [dif_pos c, dif_pos (by omega)]
      · rw [dif_neg c, dif_neg (by omega)]
  rw [e] at st
  exact st

theorem copies_local (w : Fin 5 → List Bool) (Q : Fin 5 → ℕ) (R : ℕ) (B : Fin 13 → List Bool)
    (hsrc : ∀ i : Fin 5, B ⟨i.val, by omega⟩ = ZeroPadding.pad (Q i) (frame (w i)))
    (hblank : ∀ j : Fin 13, 5 ≤ j.val → B j = List.replicate R false)
    (hR : ∀ i, 2 * (w i).length + 1 ≤ R) :
    Step copiesM (copiesCost w) (fun _ => 0) B (fun _ => 0) (bankAt w R B 7) := by
  have s0 := stepAt w Q R B hsrc hblank hR 0 (by omega)
  rw [bankAt_zero] at s0
  exact s0.seq ((stepAt w Q R B hsrc hblank hR 1 (by omega)).seq ((stepAt w Q R B hsrc hblank hR 2 (by omega)).seq
    ((stepAt w Q R B hsrc hblank hR 3 (by omega)).seq ((stepAt w Q R B hsrc hblank hR 4 (by omega)).seq
      ((stepAt w Q R B hsrc hblank hR 5 (by omega)).seq (stepAt w Q R B hsrc hblank hR 6 (by omega)))))))

theorem copies_run {U : ℕ} (sl : Fin 13 → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → ℕ) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (w : Fin 5 → List Bool) (Q : Fin 5 → ℕ) (R : ℕ)
    (hsrc : ∀ i : Fin 5, A (sl ⟨i.val, by omega⟩) = ZeroPadding.pad (Q i) (frame (w i)))
    (hblank : ∀ j : Fin 13, 5 ≤ j.val → A (sl j) = List.replicate R false)
    (hR : ∀ i, 2 * (w i).length + 1 ≤ R) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl copiesM) (copiesCost w) H A H A' ∧
      (∀ i : Fin 7, A' (sl (tgtP i)) = ZeroPadding.pad R (frame (w (srcIx i)))) ∧
      ∀ x, (∀ j : Fin 13, sl j = x → j.val < 5 ∨ 12 ≤ j.val) → A' x = A x := by
  have loc := copies_local w Q R (fun j => A (sl j)) hsrc hblank hR
  have sf := loc.focus sl hsl H A
  have eH : dockH sl H (fun _ => 0) = H := by
    funext x
    by_cases hx : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [dockH_slot _ hsl, hH]
    · simp only [not_exists] at hx
      exact dockH_other _ _ _ _ hx
  have eIn : install sl A (fun j => A (sl j)) = A := install_existing sl A _ (fun _ => rfl)
  rw [eH, eIn] at sf
  refine ⟨_, sf, ?_, ?_⟩
  · intro i
    rw [install_slot _ hsl]
    unfold bankAt
    rw [dif_pos (by simp [tgtP]; omega)]
    congr 4
    exact Fin.ext (by simp [tgtP])
  · intro x hx
    by_cases hx' : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hx'
      rw [install_slot _ hsl]
      unfold bankAt
      rw [dif_neg (by have := hx j rfl; omega)]
    · simp only [not_exists] at hx'
      exact install_other _ _ _ _ hx'

end
end NearCubicWires.SourceResident

