import Proof.SourceAssembly.SourceInv

/-! # The per-call driver refresh: `cs 2` and `drv 0, 1, 2, 4` rebuilt from resident masters

**Consumer.** `SourceCyclePad.cycle_prepared_pad`'s `hU0`, `hS`, `hR`, `hB`, `hv`, `hdH` and `hcsH` (`k = 2`) at the refill
prologue's exit. The cycle's frame exports nothing on `cs`/`drv` tapes (see `SourceInv`), so the refill prologue
`clear ; rest ; refresh` rebuilds these five tapes every call: `refreshMachine` clears `rfT 0..4 = B+14..B+18` (the
H1 clear, docked with the resident driver/log `scr 11/12`), copies each master `mT i` onto `rfT i`
(`RecoveryBoundedTapeCopy.copy_ready`, driver/log `scr 11/12`), then moves the four driver heads to `1`.

Also here: `Refill.clear_on`, the H1 clear on ANY injective clear map (the proof of
`SourceClearBound.clear_on_layout`, generalized).

**Paper.** Input processing inside the call (`paper.tex:721-733`). **Budget**: `refreshCost Rc =
(4Rc+7) + 5·((2Rc+4)+1) + 2`, TABLE class through `Rc` (the class of the per-call clear,
`SourceCleanupClass.perCall_class`).
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction
noncomputable section

namespace Refill

/-- **The clear on ANY clear set** `clr` (stage tapes, then its driver, then its log): arbitrary words and heads
`≤ R` on the stage tapes become `replicate R false` with head 0; driver, log and every other tape are kept. -/
theorem clear_on {t U : Nat} (clr : Fin (t+1+1) → Fin U) (hclr : Function.Injective clr) (R : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ i : Fin t, H (clr (Fin.castAdd 1 (Fin.castAdd 1 i))) ≤ R)
    (hA : ∀ i : Fin t, (A (clr (Fin.castAdd 1 (Fin.castAdd 1 i)))).length ≤ R)
    (hdH : H (clr (Fin.castAdd 1 ((0 : Fin 1).natAdd t))) = 0)
    (hlH : H (clr ((0 : Fin 1).natAdd (t + 1))) = 0)
    (hd : A (clr (Fin.castAdd 1 ((0 : Fin 1).natAdd t))) = List.replicate R true)
    (hl : A (clr ((0 : Fin 1).natAdd (t + 1))) = List.replicate (R+2) false) :
    Step (RecoveryFocus.machine clr (PCJ6e421fabe2aa4155_SourceClear.machine t)) (4*R+7)
      H A (dockH clr H (fun _ => 0))
      (install clr A
        (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate R false) (List.replicate R true)
          (List.replicate (R+2) false))) := by
  let Z : Fin t → List Bool := fun i => A (clr (Fin.castAdd 1 (Fin.castAdd 1 i)))
  let HZ : Fin t → Nat := fun i => H (clr (Fin.castAdd 1 (Fin.castAdd 1 i)))
  have hloc := clear_local t R Z HZ hH hA
  refine hloc.dock clr hclr H A ?_ ?_
  · intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp [PCJ6e421fabe2aa4155_SourceClear.join, HZ]
      · rw [Fin.eq_zero k]; simpa [PCJ6e421fabe2aa4155_SourceClear.join] using hdH
    · rw [Fin.eq_zero k]; simpa [PCJ6e421fabe2aa4155_SourceClear.join] using hlH
  · intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp [PCJ6e421fabe2aa4155_SourceClear.join, Z]
      · rw [Fin.eq_zero k]; simpa [PCJ6e421fabe2aa4155_SourceClear.join] using hd
    · rw [Fin.eq_zero k]; simpa [PCJ6e421fabe2aa4155_SourceClear.join] using hl

end Refill

namespace Rest

/-- One whole-word copy `src → dst` with the resident driver `1^Rc` and log `0^(Rc+2)`, all four heads 0. -/
theorem copy_one {V : Nat} (src dst drv log : Fin V)
    (h1 : src ≠ dst) (h2 : src ≠ drv) (h3 : src ≠ log) (h4 : dst ≠ drv) (h5 : dst ≠ log) (h6 : drv ≠ log)
    (Rc : Nat) (w : List Bool) (hw : w.length = Rc) (H : Fin V → Nat) (A : Fin V → List Bool)
    (hsrc : A src = w) (hdst : A dst = List.replicate Rc false) (hdrv : A drv = List.replicate Rc true)
    (hlog : A log = List.replicate (Rc+2) false)
    (hHs : H src = 0) (hHd : H dst = 0) (hHv : H drv = 0) (hHl : H log = 0) :
    ∃ A', Step (RecoveryFocus.machine (![src, dst, drv, log] : Fin 4 → Fin V) RecoveryBoundedTapeCopy.machine)
      (2*Rc+4) H A H A' ∧ A' dst = w ∧ (∀ x, x ≠ dst → A' x = A x) := by
  let s2 : Fin 4 → Fin V := ![src, dst, drv, log]
  have i2 : Function.Injective s2 := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [s2]
  have c0 := RecoveryChildSelection.ReadyRun.pad (RecoveryBoundedTapeCopy.copy_ready w Rc (Rc+2)) ![0, Rc, 0, 0]
  have e2 := Step.of_ready c0
  have st2 := Prologue.dockKeep e2 s2 i2 H A (by
    intro j; fin_cases j <;> assumption) (by
    intro j; fin_cases j
    · show A src = _; simp [hsrc]
    · show A dst = _; simp [hdst, ZeroPadding.pad]
    · show A drv = _; simp [hdrv]
    · show A log = _; simp [hlog])
  refine ⟨_, st2, ?_, ?_⟩
  · rw [show install s2 A _ dst = _ from install_slot s2 i2 A _ 1]
    simp only [Matrix.cons_val_one]
    rw [← hw, Prologue.copied_full]
    simp [ZeroPadding.pad]
  · intro x hx
    by_cases hs : x = src
    · subst hs
      rw [show install s2 A _ x = _ from install_slot s2 i2 A _ 0]; simp [hsrc]
    by_cases hv : x = drv
    · subst hv
      rw [show install s2 A _ x = _ from install_slot s2 i2 A _ 2]; simp [hdrv]
    by_cases hl : x = log
    · subst hl
      rw [show install s2 A _ x = _ from install_slot s2 i2 A _ 3]
      simp [hlog]
    exact install_other s2 A _ x (by intro j; fin_cases j <;> simp [s2] <;> intro h <;> simp_all)

variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt2 eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- The refresh's clear map, by value: `B+14 .. B+18`, then `scr 11`, `scr 12`. -/
def clr5V (d : SourceConstruction.Dims) (k : Nat) : Nat :=
  if k < 5 then d.B + 14 + k else if k = 5 then d.scrV 11 else d.scrV 12

def clr5 : Fin (5+1+1) → Fin V := fun k =>
  ⟨clr5V d k.val, Nat.lt_of_lt_of_le (by
    have := k.isLt; have := e.hres2
    simp only [clr5V, SourceConstruction.Dims.scrV, SourceConstruction.Dims.B, SourceConstruction.Dims.U,
      SourceConstruction.Dims.G, SourceConstruction.Dims.prepT]
    split_ifs <;> omega) hV⟩

theorem clr5_injective : Function.Injective (clr5 e hV) := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt; have hb := b.isLt
  simp only [clr5, clr5V, SourceConstruction.Dims.scrV, SourceConstruction.Dims.B] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem clr5_stage (i : Fin 5) : clr5 e hV (Fin.castAdd 1 (Fin.castAdd 1 i)) = Dims.rfT e hV i := by
  apply Fin.ext
  have := i.isLt
  simp only [clr5, clr5V, Dims.rfT, Fin.val_castAdd]
  simp [this]

theorem clr5_driver : clr5 e hV (Fin.castAdd 1 ((0 : Fin 1).natAdd 5)) = d.scr hV 11 := by
  apply Fin.ext; simp [clr5, clr5V, SourceConstruction.Dims.scr]

theorem clr5_log : clr5 e hV ((0 : Fin 1).natAdd (5 + 1)) = d.scr hV 12 := by
  apply Fin.ext; simp [clr5, clr5V, SourceConstruction.Dims.scr]

/-- A tape is a refresh target iff its value is in `B+14 .. B+18`. -/
theorem rfT_val (i : Fin 5) : (Dims.rfT e hV i).val = d.B + 14 + i.val := rfl

theorem scr_ne_rfT (m : Nat) (hm : m = 11 ∨ m = 12) (i : Fin 5) : (d.scr hV ⟨m, by omega⟩) ≠ Dims.rfT e hV i := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  simp only [SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV, Dims.rfT, SourceConstruction.Dims.B] at hv
  omega

theorem mT_ne_rfT (i k : Fin 5) : Dims.mT e hV i ≠ Dims.rfT e hV k := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt; have := k.isLt
  simp only [Dims.mT, Dims.rfT, restPc] at hv
  omega

theorem mT_ne_scr (i : Fin 5) (m : Nat) (hm : m = 11 ∨ m = 12) : Dims.mT e hV i ≠ d.scr hV ⟨m, by omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Dims.mT, SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV, SourceConstruction.Dims.B,
    restPc] at hv
  omega

theorem scr11_ne_scr12 : d.scr hV 11 ≠ d.scr hV 12 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV] at hv
  omega

/-- The copy of master `i` onto target `i`. -/
def copyM (i : Fin 5) :=
  RecoveryFocus.machine (![Dims.mT e hV i, Dims.rfT e hV i, d.scr hV 11, d.scr hV 12] : Fin 4 → Fin V)
    RecoveryBoundedTapeCopy.machine

/-- The four driver heads move right by one. -/
def moveDirs : Fin V → HeadMove := fun x =>
  if d.B + 15 ≤ x.val ∧ x.val ≤ d.B + 18 then HeadMove.right else HeadMove.stay

def moveM := DecompositionCountPosition.move (moveDirs (d := d) (V := V))

/-- **The refresh machine.** ONE fixed machine from the layout. -/
def refreshMachine :=
  Composition.machine (RecoveryFocus.machine (clr5 e hV) (PCJ6e421fabe2aa4155_SourceClear.machine 5))
    (Composition.machine (copyM e hV 0) (Composition.machine (copyM e hV 1)
      (Composition.machine (copyM e hV 2) (Composition.machine (copyM e hV 3)
        (Composition.machine (copyM e hV 4) (moveM (d := d) (V := V)))))))

/-- Its cost: the clear, five copies, one move. -/
def refreshCost (Rc : Nat) : Nat :=
  (4*Rc+7) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + 1)))))

/-- **The refresh run.** From any bank whose five targets are dirt-bounded by `Rc`, with the resident driver/log
and masters of length `Rc`: the targets hold the masters, heads `0` on `cs 2` and `1` on the four drivers; every
other tape (word and head) is kept. -/
theorem refresh_run (Rc : Nat) (M : Fin 5 → List Bool) (hM : ∀ i, (M i).length = Rc)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hA : ∀ i, (A (Dims.rfT e hV i)).length ≤ Rc) (hH : ∀ i, H (Dims.rfT e hV i) ≤ Rc)
    (hdrv : A (d.scr hV 11) = List.replicate Rc true) (hdrvH : H (d.scr hV 11) = 0)
    (hlg : A (d.scr hV 12) = List.replicate (Rc+2) false) (hlgH : H (d.scr hV 12) = 0)
    (hm : ∀ i, A (Dims.mT e hV i) = M i) (hmH : ∀ i, H (Dims.mT e hV i) = 0) :
    ∃ (H' : Fin V → Nat) (A' : Fin V → List Bool), Step (refreshMachine e hV) (refreshCost Rc) H A H' A' ∧
      (∀ i, A' (Dims.rfT e hV i) = M i) ∧ H' (Dims.rfT e hV 0) = 0 ∧
      (∀ i : Fin 5, i.val ≠ 0 → H' (Dims.rfT e hV i) = 1) ∧
      (∀ x, (∀ i, Dims.rfT e hV i ≠ x) → A' x = A x ∧ H' x = H x) := by
  classical
  -- 1. the clear
  have sC := Refill.clear_on (clr5 e hV) (clr5_injective e hV) Rc H A
    (fun i => by rw [clr5_stage]; exact hH i) (fun i => by rw [clr5_stage]; exact hA i)
    (by rw [clr5_driver]; exact hdrvH) (by rw [clr5_log]; exact hlgH)
    (by rw [clr5_driver]; exact hdrv) (by rw [clr5_log]; exact hlg)
  set H1 := dockH (clr5 e hV) H (fun _ => 0) with hH1
  set A1 := install (clr5 e hV) A (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false)
    (List.replicate Rc true) (List.replicate (Rc+2) false)) with hA1
  have A1t : ∀ i, A1 (Dims.rfT e hV i) = List.replicate Rc false := by
    intro i
    rw [← clr5_stage e hV i, hA1, install_slot _ (clr5_injective e hV)]
    simp [PCJ6e421fabe2aa4155_SourceClear.join]
  have H1t : ∀ i, H1 (Dims.rfT e hV i) = 0 := by
    intro i
    rw [← clr5_stage e hV i, hH1, dockH_slot _ (clr5_injective e hV)]
  have A1d : A1 (d.scr hV 11) = List.replicate Rc true := by
    rw [← clr5_driver e hV, hA1, install_slot _ (clr5_injective e hV), PCJ6e421fabe2aa4155_SourceClear.join,
      Fin.addCases_left, Fin.addCases_right]
  have A1l : A1 (d.scr hV 12) = List.replicate (Rc+2) false := by
    rw [← clr5_log e hV, hA1, install_slot _ (clr5_injective e hV), PCJ6e421fabe2aa4155_SourceClear.join,
      Fin.addCases_right]
  have H1d : H1 (d.scr hV 11) = 0 := by rw [← clr5_driver e hV, hH1, dockH_slot _ (clr5_injective e hV)]
  have H1l : H1 (d.scr hV 12) = 0 := by rw [← clr5_log e hV, hH1, dockH_slot _ (clr5_injective e hV)]
  have off5 : ∀ x, (∀ i, Dims.rfT e hV i ≠ x) → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 → ∀ k, clr5 e hV k ≠ x := by
    intro x h1 h2 h3 k hk
    have hkv := k.isLt
    by_cases hk5 : k.val < 5
    · have e1 : k = Fin.castAdd 1 (Fin.castAdd 1 ⟨k.val, hk5⟩) := Fin.ext rfl
      rw [e1, clr5_stage] at hk; exact h1 _ hk
    by_cases hk6 : k.val = 5
    · have e1 : k = Fin.castAdd 1 ((0 : Fin 1).natAdd 5) := Fin.ext (by simp [hk6])
      rw [e1, clr5_driver] at hk; exact h2 hk.symm
    · have e1 : k = (0 : Fin 1).natAdd (5 + 1) := Fin.ext (by simp; omega)
      rw [e1, clr5_log] at hk; exact h3 hk.symm
  have A1o : ∀ x, (∀ i, Dims.rfT e hV i ≠ x) → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 → A1 x = A x :=
    fun x h1 h2 h3 => install_other _ A _ x (off5 x h1 h2 h3)
  have H1o : ∀ x, (∀ i, Dims.rfT e hV i ≠ x) → x ≠ d.scr hV 11 → x ≠ d.scr hV 12 → H1 x = H x :=
    fun x h1 h2 h3 => dockH_other _ H _ x (off5 x h1 h2 h3)
  have A1m : ∀ i, A1 (Dims.mT e hV i) = M i := fun i =>
    (A1o _ (fun k => (mT_ne_rfT e hV i k).symm) (mT_ne_scr e hV i 11 (Or.inl rfl))
      (mT_ne_scr e hV i 12 (Or.inr rfl))).trans (hm i)
  have H1m : ∀ i, H1 (Dims.mT e hV i) = 0 := fun i =>
    (H1o _ (fun k => (mT_ne_rfT e hV i k).symm) (mT_ne_scr e hV i 11 (Or.inl rfl))
      (mT_ne_scr e hV i 12 (Or.inr rfl))).trans (hmH i)
  -- 2. the five copies (heads unchanged: `H1` throughout)
  have n11 := scr_ne_rfT e hV 11 (Or.inl rfl)
  have n12 := scr_ne_rfT e hV 12 (Or.inr rfl)
  have cp : ∀ (i : Fin 5) (B0 : Fin V → List Bool), B0 (Dims.mT e hV i) = M i →
      B0 (Dims.rfT e hV i) = List.replicate Rc false → B0 (d.scr hV 11) = List.replicate Rc true →
      B0 (d.scr hV 12) = List.replicate (Rc+2) false →
      ∃ B1, Step (copyM e hV i) (2*Rc+4) H1 B0 H1 B1 ∧ B1 (Dims.rfT e hV i) = M i ∧
        (∀ x, x ≠ Dims.rfT e hV i → B1 x = B0 x) := by
    intro i B0 b1 b2 b3 b4
    exact copy_one _ _ _ _ (mT_ne_rfT e hV i i) (mT_ne_scr e hV i 11 (Or.inl rfl))
      (mT_ne_scr e hV i 12 (Or.inr rfl)) (fun h => n11 i h.symm) (fun h => n12 i h.symm)
      (scr11_ne_scr12 hV) Rc (M i) (hM i) H1 B0 b1 b2 b3 b4 (H1m i) (H1t i) H1d H1l
  have rne : ∀ i k : Fin 5, i ≠ k → Dims.rfT e hV i ≠ Dims.rfT e hV k :=
    fun i k h hh => h (Dims.rfT_injective e hV hh)
  -- copy 0
  obtain ⟨B1, s1, b1t, b1o⟩ := cp 0 A1 (A1m 0) (A1t 0) A1d A1l
  have B1v : ∀ x, x ≠ Dims.rfT e hV 0 → B1 x = A1 x := b1o
  obtain ⟨B2, s2, b2t, b2o⟩ := cp 1 B1 ((B1v _ (mT_ne_rfT e hV 1 0)).trans (A1m 1))
    ((B1v _ (rne 1 0 (by decide))).trans (A1t 1)) ((B1v _ (n11 0)).trans A1d) ((B1v _ (n12 0)).trans A1l)
  obtain ⟨B3, s3, b3t, b3o⟩ := cp 2 B2
    ((b2o _ (mT_ne_rfT e hV 2 1)).trans ((B1v _ (mT_ne_rfT e hV 2 0)).trans (A1m 2)))
    ((b2o _ (rne 2 1 (by decide))).trans ((B1v _ (rne 2 0 (by decide))).trans (A1t 2)))
    ((b2o _ (n11 1)).trans ((B1v _ (n11 0)).trans A1d)) ((b2o _ (n12 1)).trans ((B1v _ (n12 0)).trans A1l))
  obtain ⟨B4, s4, b4t, b4o⟩ := cp 3 B3
    ((b3o _ (mT_ne_rfT e hV 3 2)).trans ((b2o _ (mT_ne_rfT e hV 3 1)).trans
      ((B1v _ (mT_ne_rfT e hV 3 0)).trans (A1m 3))))
    ((b3o _ (rne 3 2 (by decide))).trans ((b2o _ (rne 3 1 (by decide))).trans
      ((B1v _ (rne 3 0 (by decide))).trans (A1t 3))))
    ((b3o _ (n11 2)).trans ((b2o _ (n11 1)).trans ((B1v _ (n11 0)).trans A1d)))
    ((b3o _ (n12 2)).trans ((b2o _ (n12 1)).trans ((B1v _ (n12 0)).trans A1l)))
  obtain ⟨B5, s5, b5t, b5o⟩ := cp 4 B4
    ((b4o _ (mT_ne_rfT e hV 4 3)).trans ((b3o _ (mT_ne_rfT e hV 4 2)).trans ((b2o _ (mT_ne_rfT e hV 4 1)).trans
      ((B1v _ (mT_ne_rfT e hV 4 0)).trans (A1m 4)))))
    ((b4o _ (rne 4 3 (by decide))).trans ((b3o _ (rne 4 2 (by decide))).trans ((b2o _ (rne 4 1 (by decide))).trans
      ((B1v _ (rne 4 0 (by decide))).trans (A1t 4)))))
    ((b4o _ (n11 3)).trans ((b3o _ (n11 2)).trans ((b2o _ (n11 1)).trans ((B1v _ (n11 0)).trans A1d))))
    ((b4o _ (n12 3)).trans ((b3o _ (n12 2)).trans ((b2o _ (n12 1)).trans ((B1v _ (n12 0)).trans A1l))))
  -- 3. the head move
  obtain ⟨rr, hr, hf, _⟩ := DecompositionCountPosition.move_run (moveDirs (d := d) (V := V)) H1 B5
  have sM : Step (moveM (d := d) (V := V)) 1 H1 B5 (fun x => ((moveDirs (d := d) (V := V)) x).apply (H1 x)) B5 :=
    Step.of_run hr (by rw [hf]) (congrArg Configuration.tapes hf)
  refine ⟨_, _, sC.seq (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq sM))))), ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · show B5 (Dims.rfT e hV 0) = M 0
      rw [b5o _ (rne 0 4 (by decide)), b4o _ (rne 0 3 (by decide)), b3o _ (rne 0 2 (by decide)),
        b2o _ (rne 0 1 (by decide)), b1t]
    · show B5 (Dims.rfT e hV 1) = M 1
      rw [b5o _ (rne 1 4 (by decide)), b4o _ (rne 1 3 (by decide)), b3o _ (rne 1 2 (by decide)), b2t]
    · show B5 (Dims.rfT e hV 2) = M 2
      rw [b5o _ (rne 2 4 (by decide)), b4o _ (rne 2 3 (by decide)), b3t]
    · show B5 (Dims.rfT e hV 3) = M 3
      rw [b5o _ (rne 3 4 (by decide)), b4t]
    · exact b5t
  · show (moveDirs (d := d) (V := V) _).apply (H1 _) = 0
    have : ¬ (d.B + 15 ≤ (Dims.rfT e hV 0).val ∧ (Dims.rfT e hV 0).val ≤ d.B + 18) := by
      rw [rfT_val]; simp
    simp only [moveDirs, if_neg this, H1t]
    rfl
  · intro i hi
    show (moveDirs (d := d) (V := V) _).apply (H1 _) = 1
    have hl := i.isLt
    have : d.B + 15 ≤ (Dims.rfT e hV i).val ∧ (Dims.rfT e hV i).val ≤ d.B + 18 := by
      rw [rfT_val]; omega
    simp only [moveDirs, if_pos this, H1t]
    rfl
  · intro x hx
    have hxv : ¬ (d.B + 14 ≤ x.val ∧ x.val ≤ d.B + 18) := by
      intro h
      exact hx ⟨x.val - (d.B + 14), by omega⟩ (Fin.ext (by rw [rfT_val]; simp; omega))
    have kB : B5 x = A1 x := by
      rw [b5o _ (fun h => hx 4 h.symm), b4o _ (fun h => hx 3 h.symm), b3o _ (fun h => hx 2 h.symm),
        b2o _ (fun h => hx 1 h.symm), B1v _ (fun h => hx 0 h.symm)]
    have hmv : ¬ (d.B + 15 ≤ x.val ∧ x.val ≤ d.B + 18) := by omega
    constructor
    · rw [kB]
      by_cases h11 : x = d.scr hV 11
      · rw [h11, A1d, hdrv]
      by_cases h12 : x = d.scr hV 12
      · rw [h12, A1l, hlg]
      exact A1o x hx h11 h12
    · show (moveDirs (d := d) (V := V) x).apply (H1 x) = H x
      simp only [moveDirs, if_neg hmv]
      show H1 x = H x
      by_cases h11 : x = d.scr hV 11
      · rw [h11, H1d, hdrvH]
      by_cases h12 : x = d.scr hV 12
      · rw [h12, H1l, hlgH]
      exact H1o x hx h11 h12

end Rest
end
end NearCubicWires.SourceConstruction
end
