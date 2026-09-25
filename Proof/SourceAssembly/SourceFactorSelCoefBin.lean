import Proof.SourceAssembly.SourceFactorSelCoefAcc

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefBin
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc
noncomputable section

/-! ## Unary → framed binary at width `W` -/

/-- Local universe `Fin 16`: `0` `1^n` · `1` `1^W` · `2` output · `3` log · `4` copy · `5` zero summand ·
`6..14` the count's private tapes (its output word on `10`) · `15` the normalizer's flag. -/
def tobinM := Composition.machine (Count.sumM (0 : Fin 16) 5 4 3)
  (Composition.machine (RecoveryFocus.machine (![4, 6, 7, 8, 9, 10, 11, 12, 13, 14] : Fin 10 → Fin 16)
    CloseoutRowsCountBinary.machine)
  (RecoveryFocus.machine (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) ClockNormalize.machine))

def tobinCost (n W : Nat) : Nat := (2 * (n + 0) + 6) + 1 + (CloseoutRowsCountBinary.budget n + 1 + (4 * W + 4))

theorem tobin_run (n W Qi Qw R S C : Nat) (E : Fin 16 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Qi (List.replicate n true)) (h1 : E 1 = ZeroPadding.pad Qw (List.replicate W true))
    (h2 : E 2 = List.replicate R false) (h3 : E 3 = List.replicate C false)
    (hscr : ∀ j : Fin 16, 4 ≤ j.val → E j = List.replicate S false) (hC1 : n + 2 ≤ C) (hC2 : 2 * W + 1 ≤ C) :
    ∃ E' : Fin 16 → List Bool, Step tobinM (tobinCost n W) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 2 = ZeroPadding.pad R (frame (binary W n)) ∧ E' 0 = E 0 ∧ E' 1 = E 1 ∧ E' 3 = E 3 := by
  have h5 : E 5 = ZeroPadding.pad S (List.replicate 0 true) := by
    rw [hscr 5 (by decide)]; exact (pad_nil S).symm
  have s1 := Count.sum_step (0 : Fin 16) 5 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) n 0 Qi S S C (by omega) (fun _ => 0) E (fun _ _ => rfl) h0 h5 (hscr 4 (by decide)) h3
  set E1 := Function.update E (4 : Fin 16) (ZeroPadding.pad S (List.replicate (n + 0) true)) with hE1
  obtain ⟨L, lc, l5⟩ := count_local n S S
  have d2 := lc.dock (![4, 6, 7, 8, 9, 10, 11, 12, 13, 14] : Fin 10 → Fin 16) (by decide) (fun _ => 0) E1
    (fun _ => rfl) (by
      intro j; fin_cases j
      · simp [E1]
      all_goals (simp only [E1]; rw [Function.update_of_ne (by decide)]; exact hscr _ (by decide)))
  rw [dockH_existing _ (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at d2
  set E2 := install (![4, 6, 7, 8, 9, 10, 11, 12, 13, 14] : Fin 10 → Fin 16) E1 L with hE2
  have k2 : ∀ x : Fin 16, x.val < 4 ∨ x.val = 15 → E2 x = E1 x := by
    intro x hx
    apply install_other
    intro j e
    fin_cases j <;> (subst e; simp at hx)
  have g10 : E2 10 = ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)) := by
    have := install_slot (![4, 6, 7, 8, 9, 10, 11, 12, 13, 14] : Fin 10 → Fin 16) (by decide) E1 L 5
    exact this.trans l5
  have s3 := (norm_local W (CloseoutRowsCountBinary.bits n) Qw S R S C hC2).dock
    (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) (by decide) (fun _ => 0) E2 (fun _ => rfl) (by
      intro j; fin_cases j
      · show E2 1 = _; rw [k2 1 (by decide)]; simp [E1, h1]
      · exact g10
      · show E2 2 = _; rw [k2 2 (by decide)]; simp [E1, h2]
      · show E2 15 = _; rw [k2 15 (by decide)]; simp [E1, hscr 15 (by decide)]
      · show E2 3 = _; rw [k2 3 (by decide)]; simp [E1, h3])
  rw [dockH_existing _ (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at s3
  have hall : Step tobinM _ (fun _ => 0) E (fun _ => 0) _ := s1.seq (d2.seq s3)
  refine ⟨_, hall, ?_, ?_, ?_, ?_⟩
  · have this : install (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) E2 ![ZeroPadding.pad Qw (List.replicate W true), ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)),
          ZeroPadding.pad R (frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits n))),
          ZeroPadding.pad S [decide ((CloseoutRowsCountBinary.bits n).length ≤ W)], List.replicate C false] (2 : Fin 16) =
        (![ZeroPadding.pad Qw (List.replicate W true), ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)),
          ZeroPadding.pad R (frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits n))),
          ZeroPadding.pad S [decide ((CloseoutRowsCountBinary.bits n).length ≤ W)], List.replicate C false] : Fin 5 → List Bool) 2 :=
      install_slot (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) (by decide) E2 _ 2
    rw [this]
    show ZeroPadding.pad R (frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits n))) = _
    rw [resize_bits]
  · rw [install_other _ _ _ _ (by decide), k2 0 (by decide)]
    simp [E1]
  · have this : install (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) E2 ![ZeroPadding.pad Qw (List.replicate W true), ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)),
          ZeroPadding.pad R (frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits n))),
          ZeroPadding.pad S [decide ((CloseoutRowsCountBinary.bits n).length ≤ W)], List.replicate C false] (1 : Fin 16) =
        (![ZeroPadding.pad Qw (List.replicate W true), ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)),
          ZeroPadding.pad R (frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits n))),
          ZeroPadding.pad S [decide ((CloseoutRowsCountBinary.bits n).length ≤ W)], List.replicate C false] : Fin 5 → List Bool) 0 :=
      install_slot (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) (by decide) E2 _ 0
    rw [this]
    show ZeroPadding.pad Qw (List.replicate W true) = _
    rw [h1]
  · have this : install (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) E2 ![ZeroPadding.pad Qw (List.replicate W true), ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)),
          ZeroPadding.pad R (frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits n))),
          ZeroPadding.pad S [decide ((CloseoutRowsCountBinary.bits n).length ≤ W)], List.replicate C false] (3 : Fin 16) =
        (![ZeroPadding.pad Qw (List.replicate W true), ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)),
          ZeroPadding.pad R (frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits n))),
          ZeroPadding.pad S [decide ((CloseoutRowsCountBinary.bits n).length ≤ W)], List.replicate C false] : Fin 5 → List Bool) 4 :=
      install_slot (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) (by decide) E2 _ 4
    rw [this]
    show List.replicate C false = _
    rw [h3]

/-- `tobin_run`, docked by an injective `sl : Fin 16 → Fin U`. -/
theorem tobin_step {U : Nat} (sl : Fin 16 → Fin U) (hsl : Function.Injective sl) (n W Qi Qw R S C : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qi (List.replicate n true))
    (h1 : A (sl 1) = ZeroPadding.pad Qw (List.replicate W true))
    (h2 : A (sl 2) = List.replicate R false) (h3 : A (sl 3) = List.replicate C false)
    (hscr : ∀ j : Fin 16, 4 ≤ j.val → A (sl j) = List.replicate S false) (hC1 : n + 2 ≤ C) (hC2 : 2 * W + 1 ≤ C) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl tobinM) (tobinCost n W) H A H A' ∧
      A' (sl 2) = ZeroPadding.pad R (frame (binary W n)) ∧ (∀ x, x ≠ sl 2 → (∀ j : Fin 16, 4 ≤ j.val → sl j ≠ x) →
        A' x = A x) := by
  obtain ⟨E', hs, ho, e0, e1, e3⟩ := tobin_run n W Qi Qw R S C (fun j => A (sl j)) h0 h1 h2 h3 hscr hC1 hC2
  have d := hs.dock sl hsl H A (fun j => hH j) (fun j => rfl)
  rw [dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, by rw [install_slot sl hsl]; exact ho, ?_⟩
  intro x hx2 hxs
  by_cases hx : ∃ j, sl j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [install_slot sl hsl]
    have hj : j.val < 4 := by
      by_contra hc
      exact hxs j (by omega) rfl
    have hj2 : j ≠ 2 := fun e => hx2 (by rw [e])
    fin_cases j
    · exact e0
    · exact e1
    · exact absurd rfl hj2
    · exact e3
    all_goals (simp at hj)
  · exact install_other sl A E' x (fun j e => hx ⟨j, e⟩)

/-! ## One switched factor slot -/

/-- The accumulator on the first thirty tapes of `Fin 32`. -/
def accIn : Fin 30 → Fin 32 := fun j => j.castAdd 2

theorem accIn_inj : Function.Injective accIn := fun a b h => by
  simp only [accIn] at h
  exact Fin.castAdd_injective 30 2 h

/-- Skip branch: the factor is `1` — copy the three accumulators (zero summand on `31`). -/
def skipM := Composition.machine (Count.sumM (1 : Fin 32) 31 4 7)
  (Composition.machine (Count.sumM (2 : Fin 32) 31 5 7) (Count.sumM (3 : Fin 32) 31 6 7))

/-- Local universe `Fin 32`: `CoefAcc`'s thirty ports, `30` the slot's flag `[f]`, `31` a blank zero summand. -/
def accSwM := CloseoutRowsOriginalSwitch.machine (RecoveryFocus.machine accIn CoefAcc.accM) skipM (30 : Fin 32)

def skipCost (Na Da sa : Nat) : Nat := (2 * (Na + 0) + 6) + 1 + ((2 * (Da + 0) + 6) + 1 + (2 * (sa + 0) + 6))

def accSwCost (f s : Bool) (n d c Na Da sa : Nat) : Nat :=
  if f then CoefAcc.accCost s n d c Na Da sa + 2 else skipCost Na Da sa + 2

theorem accsw_run (f s : Bool) (n d c Qr Qa Qf S C Na Da sa : Nat) (hn : n < 2 ^ c) (hd : d < 2 ^ c)
    (E : Fin 32 → List Bool) (h0 : f = true → E 0 = recW s n d c Qr)
    (h1 : E 1 = ZeroPadding.pad Qa (List.replicate Na true)) (h2 : E 2 = ZeroPadding.pad Qa (List.replicate Da true))
    (h3 : E 3 = ZeroPadding.pad Qa (List.replicate sa true)) (h7 : E 7 = List.replicate C false)
    (h30 : E 30 = ZeroPadding.pad Qf [f])
    (hscr : ∀ j : Fin 32, (j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ (8 ≤ j.val ∧ j.val ≠ 30)) → E j = List.replicate S false)
    (hf : AccFits c n d Na Da sa S C) :
    ∃ E' : Fin 32 → List Bool, Step accSwM (accSwCost f s n d c Na Da sa) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 4 = ZeroPadding.pad S (List.replicate (Na * (if f then n else 1)) true) ∧
      E' 5 = ZeroPadding.pad S (List.replicate (Da * (if f then d else 1)) true) ∧
      E' 6 = ZeroPadding.pad S (List.replicate (sa + (if f then s.toNat else 0)) true) ∧
      (∀ j : Fin 32, j.val < 4 → E' j = E j) ∧ E' 7 = E 7 ∧ E' 30 = E 30 := by
  cases f with
  | true =>
    obtain ⟨L, hs, l4, l5, l6, lk, l7⟩ := CoefAcc.acc_run s n d c Qr Qa S C Na Da sa hn hd (fun j => E (accIn j))
      (h0 rfl) h1 h2 h3 h7 (fun j hj => hscr _ (by simp only [accIn, Fin.val_castAdd]; omega)) hf
    have dk := hs.dock accIn accIn_inj (fun _ => 0) E (fun _ => rfl) (fun _ => rfl)
    rw [dockH_existing accIn (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at dk
    have sw := CloseoutRowsOriginalSwitch.true_run _ skipM (30 : Fin 32) dk (by rw [h30]; exact Count.read_flag Qf true)
    refine ⟨_, sw, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := install_slot accIn accIn_inj E L 4
      simpa [accIn] using this.trans l4
    · have := install_slot accIn accIn_inj E L 5
      simpa [accIn] using this.trans l5
    · have := install_slot accIn accIn_inj E L 6
      simpa [accIn] using this.trans l6
    · intro j hj
      have := install_slot accIn accIn_inj E L ⟨j.val, by omega⟩
      have hj' : accIn ⟨j.val, by omega⟩ = j := Fin.ext (by simp [accIn])
      rw [hj'] at this
      rw [this, lk ⟨j.val, by omega⟩ hj]
      rw [hj']
    · have := install_slot accIn accIn_inj E L 7
      simpa [accIn] using this.trans l7
    · apply install_other
      intro j e
      have := congrArg Fin.val e
      simp [accIn] at this
      omega
  | false =>
    have z31 : E 31 = ZeroPadding.pad S (List.replicate 0 true) := by
      rw [hscr 31 (by decide)]; exact (pad_nil S).symm
    have c1 : Na + 0 + 2 ≤ C := by have := hf.c3; nlinarith
    have c2 : Da + 0 + 2 ≤ C := by have := hf.c4; nlinarith
    have c3 : sa + 0 + 2 ≤ C := by have := hf.c2; omega
    have t1 := Count.sum_step (1 : Fin 32) 31 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) Na 0 Qa S S C c1 (fun _ => 0) E (fun _ _ => rfl) h1 z31 (hscr 4 (by decide)) h7
    set F1 := Function.update E (4 : Fin 32) (ZeroPadding.pad S (List.replicate (Na + 0) true)) with hF1
    have t2 := Count.sum_step (2 : Fin 32) 31 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) Da 0 Qa S S C c2 (fun _ => 0) F1 (fun _ _ => rfl) (by simp [F1, h2]) (by simp [F1, z31])
      (by simp [F1, hscr 5 (by decide)]) (by simp [F1, h7])
    set F2 := Function.update F1 (5 : Fin 32) (ZeroPadding.pad S (List.replicate (Da + 0) true)) with hF2
    have t3 := Count.sum_step (3 : Fin 32) 31 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) sa 0 Qa S S C c3 (fun _ => 0) F2 (fun _ _ => rfl) (by simp [F1, F2, h3]) (by simp [F1, F2, z31])
      (by simp [F1, F2, hscr 6 (by decide)]) (by simp [F1, F2, h7])
    have hk : Step skipM _ (fun _ => 0) E (fun _ => 0) _ := t1.seq (t2.seq t3)
    have sw := CloseoutRowsOriginalSwitch.false_run (RecoveryFocus.machine accIn CoefAcc.accM) skipM (30 : Fin 32) hk
      (by rw [h30]; exact Count.read_flag Qf false)
    refine ⟨_, sw, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [F1, F2]
    · simp [F2]
    · simp
    · intro j hj
      have hne : ∀ c : Fin 32, 4 ≤ c.val → j ≠ c := fun c hc e => by rw [e] at hj; omega
      rw [Function.update_of_ne (hne 6 (by decide)), hF2, Function.update_of_ne (hne 5 (by decide)), hF1,
        Function.update_of_ne (hne 4 (by decide))]
    · simp [F1, F2]
    · simp [F1, F2]

end
end NearCubicWires.SourceFactorSel.CoefBin

