import Proof.SourceAssembly.SourceRequestTermCompose

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.SourceRequest.TermReaderRun
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg NearCubicWires.SourceRequest.TermCompose

/-- The reader's eight ports among its `1081` tapes. -/
def special (k : Fin 1081) : Prop :=
  k.val = 0 ∨ k.val = 188 ∨ k.val = 191 ∨ k.val = 383 ∨ k.val = 538 ∨ k.val = 370 ∨ k.val = 535 ∨ k.val = 1079

instance (k : Fin 1081) : Decidable (special k) := by unfold special; infer_instance

/-- The reader's scratch in the host layout: every non-port slot. -/
def scr {U : Nat} (slots : Fin 1081 → Fin U) (x : Fin U) : Prop := ∃ k, ¬ special k ∧ slots k = x

theorem entry_short (bits : List Bool) (j i cwid cw : Nat) (k : Fin 1081) (hk : ¬ special k) :
    TermCompose.entry bits j i cwid cw k = [] ∨ TermCompose.entry bits j i cwid cw k = [false] := by
  unfold special at hk
  unfold TermCompose.entry
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem pad_short (R : Nat) (hR : 1 ≤ R) (w : List Bool) (hw : w = [] ∨ w = [false]) :
    ZeroPadding.pad R w = List.replicate R false := by
  rcases hw with rfl | rfl
  · simp [ZeroPadding.pad]
  · obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    simp [ZeroPadding.pad, List.replicate_succ]

open TermReader in
/-- **The term reader, docked anywhere, meets `ReaderRun`.** -/
theorem readerRun {U : Nat} (slots : Fin 1081 → Fin U) (hinj : Function.Injective slots) (cwid cw : Nat) :
    ReaderRun (RecoveryFocus.machine slots machine) (fun bits j i => readerCost bits j i cwid cw) cwid cw
      (slots 0) (slots 188) (slots 191) (slots 383) (slots 538) (slots 370) (slots 535) (slots 1079)
      (scr slots) := by
  intro bits j i Rw R ts H A hraw hi hw hwH hj hjH hiT hiH hwid hwidH hcw hcwH hscr hcost
  obtain ⟨X, sX, x0, x188, x191, x383, x538, x370, x535, x1079⟩ := reader_exact bits j i cwid cw ts hraw hi
  have hR : 1 ≤ R := by omega
  let cap : Fin 1081 → Nat := fun k => if k.val = 0 then Rw else R
  have sp := sX.pad cap
  have hscrK : ∀ k, ¬ special k → A (slots k) = List.replicate R false ∧ H (slots k) = 0 :=
    fun k hk => hscr _ (Or.inl ⟨k, hk, rfl⟩)
  have hA : ∀ k, A (slots k) = ZeroPadding.pad (cap k) (TermCompose.entry bits j i cwid cw k) := by
    intro k
    by_cases hk : special k
    · have hk' := hk
      unfold special at hk'
      rcases hk' with h | h | h | h | h | h | h | h
      · have e : k = 0 := Fin.ext h
        subst e; rw [hw]; rfl
      · have e : k = 188 := Fin.ext h
        subst e; rw [hj]; rfl
      · have e : k = 191 := Fin.ext h
        subst e; rw [hiT]; rfl
      · have e : k = 383 := Fin.ext h
        subst e; rw [hwid]; rfl
      · have e : k = 538 := Fin.ext h
        subst e; rw [hcw]; rfl
      · have e : k = 370 := Fin.ext h
        subst e; rw [(hscr _ (Or.inr (Or.inl rfl))).1]; exact (pad_short R hR _ (Or.inl rfl)).symm
      · have e : k = 535 := Fin.ext h
        subst e; rw [(hscr _ (Or.inr (Or.inr (Or.inl rfl)))).1]; exact (pad_short R hR _ (Or.inl rfl)).symm
      · have e : k = 1079 := Fin.ext h
        subst e; rw [(hscr _ (Or.inr (Or.inr (Or.inr rfl)))).1]; exact (pad_short R hR _ (Or.inl rfl)).symm
    · rw [(hscrK k hk).1]
      have hc : cap k = R := by
        simp only [cap]; unfold special at hk; rw [if_neg (by omega)]
      rw [hc]
      exact (pad_short R hR _ (entry_short bits j i cwid cw k hk)).symm
  have hH : ∀ k, H (slots k) = 0 := by
    intro k
    by_cases hk : special k
    · unfold special at hk
      rcases hk with h | h | h | h | h | h | h | h
      · rw [show k = 0 from Fin.ext h]; exact hwH
      · rw [show k = 188 from Fin.ext h]; exact hjH
      · rw [show k = 191 from Fin.ext h]; exact hiH
      · rw [show k = 383 from Fin.ext h]; exact hwidH
      · rw [show k = 538 from Fin.ext h]; exact hcwH
      · rw [show k = 370 from Fin.ext h]; exact (hscr _ (Or.inr (Or.inl rfl))).2
      · rw [show k = 535 from Fin.ext h]; exact (hscr _ (Or.inr (Or.inr (Or.inl rfl)))).2
      · rw [show k = 1079 from Fin.ext h]; exact (hscr _ (Or.inr (Or.inr (Or.inr rfl)))).2
    · exact (hscrK k hk).2
  have d := dock sp slots hinj H A hH hA
  refine ⟨H, _, d, ?_, hH 370, ?_, hH 535, ?_, hH 1079, ?_, ?_⟩
  · rw [install_slot _ hinj, x370]; rfl
  · rw [install_slot _ hinj, x535]; rfl
  · rw [install_slot _ hinj, x1079]; rfl
  · intro x hx h1 h2 h3
    refine ⟨?_, rfl⟩
    by_cases hr : ∃ k, slots k = x
    · obtain ⟨k, rfl⟩ := hr
      have hk : special k := by
        by_contra hn; exact hx ⟨k, hn, rfl⟩
      rw [install_slot _ hinj, (hA k)]
      have hne370 : k ≠ 370 := fun e => h1 (by rw [e])
      have hne535 : k ≠ 535 := fun e => h2 (by rw [e])
      have hne1079 : k ≠ 1079 := fun e => h3 (by rw [e])
      unfold special at hk
      rcases hk with h | h | h | h | h | h | h | h
      · rw [show k = 0 from Fin.ext h, x0]; rfl
      · rw [show k = 188 from Fin.ext h, x188]; rfl
      · rw [show k = 191 from Fin.ext h, x191]; rfl
      · rw [show k = 383 from Fin.ext h, x383]; rfl
      · rw [show k = 538 from Fin.ext h, x538]; rfl
      · exact absurd (Fin.ext h) hne370
      · exact absurd (Fin.ext h) hne535
      · exact absurd (Fin.ext h) hne1079
    · simp only [not_exists] at hr
      exact install_other _ _ _ _ hr
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [install_slot _ hinj]
    have hc : cap k = R := by
      simp only [cap]; unfold special at hk; rw [if_neg (by omega)]
    rw [hc, ZeroPadding.pad_length]
    have hl := P1Closure.LocalSupport.step_fits sX k R
      (by rcases entry_short bits j i cwid cw k hk with h | h <;> rw [h] <;> simp <;> omega) (by simpa using hcost)
    exact max_le (le_refl R) hl

end NearCubicWires.SourceRequest.TermReaderRun

