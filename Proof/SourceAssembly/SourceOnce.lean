import Proof.SourceAssembly.SourceDimension

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.Once
noncomputable section
open Dimension

variable (hR hV : ℕ)

/-- The copier's four tapes: the pipeline's `Rc`, a blank scratch `b0`, the driver, the log. -/
def copySlots {U : ℕ} (ds : Fin (P hR hV) → Fin U) (b0 drv log : Fin U) : Fin 4 → Fin U :=
  ![ds (pR hR hV), b0, drv, log]

/-- The one-time producer (the guard's blank branch). -/
def onceMachine {U : ℕ} (L C cVc : ℕ) (ds : Fin (P hR hV) → Fin U) (b0 drv log : Fin U)
    (mask : Fin U → Bool) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine ds (Dimension.machine hR hV L C cVc))
    (RecoveryFocus.machine (copySlots hR hV ds b0 drv log) ClockUnarySum.machine))
    (CloseoutWitness.SelectedErase.machine mask drv log)

/-- The clear capacity. -/
abbrev Rc (L C q : ℕ) : ℕ := C * RuntimeShape.tableClass L hR q

def onceCost (L C cVc q : ℕ) : ℕ :=
  (Dimension.cost hR hV L C cVc q + 1 + (2*Rc hR L C q+6)) + 1 + (2*Rc hR L C q+4)

theorem copySlots_injective {U : ℕ} (ds : Fin (P hR hV) → Fin U) (b0 drv log : Fin U)
    (hb0 : ∀ x, ds x ≠ b0) (hdr : ∀ x, ds x ≠ drv) (hlg : ∀ x, ds x ≠ log)
    (hbd : b0 ≠ drv) (hbl : b0 ≠ log) (hdl : drv ≠ log) :
    Function.Injective (copySlots hR hV ds b0 drv log) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [copySlots] at h ⊢
  all_goals first
    | exact absurd h (hb0 _) | exact absurd h.symm (hb0 _)
    | exact absurd h (hdr _) | exact absurd h.symm (hdr _)
    | exact absurd h (hlg _) | exact absurd h.symm (hlg _)
    | exact absurd h hbd | exact absurd h.symm hbd
    | exact absurd h hbl | exact absurd h.symm hbl
    | exact absurd h hdl | exact absurd h.symm hdl

/-- **The one-time producer.**

Premises:
- the ambient carries the pipeline's input along `ds` (the arity template on `ds pq`, blank
  elsewhere), heads `0`;
- `b0`, the driver and the log are blank at head `0`;
- `mask` may select any pipeline port except the kept `pq pRl pV pVl`, plus `b0`, plus other tapes of
  length `≤ Rc` at head `0` (`hother`). The layout instance selects ALL the rest, so that every tape
  at or above `F` ends with length `≥ Rc`;
- `hfit` is the erasure condition (`prefix_le_Rc`).

Conclusion:
- the driver is `1^Rc` and the log is `0^(Rc+2)`;
- every selected tape is exactly `replicate Rc false`;
- the arity, the long `Rc` log, `V` and its log are as the pipeline left them;
- nothing else and no head moves. -/
theorem once_run (L C cVc q : ℕ) {U : ℕ} (ds : Fin (P hR hV) → Fin U) (hds : Function.Injective ds)
    (b0 drv log : Fin U) (hb0 : ∀ x, ds x ≠ b0) (hdr : ∀ x, ds x ≠ drv) (hlg : ∀ x, ds x ≠ log)
    (hbd : b0 ≠ drv) (hbl : b0 ≠ log) (hdl : drv ≠ log)
    (mask : Fin U → Bool)
    (hmq : mask (ds (pq hR hV)) = false) (hmRl : mask (ds (pRl hR hV)) = false)
    (hmV : mask (ds (pV hR hV)) = false) (hmVl : mask (ds (pVl hR hV)) = false)
    (hmd : mask drv = false) (hml : mask log = false)
    (H : Fin U → ℕ) (A : Fin U → List Bool)
    (hHds : ∀ x, H (ds x) = 0) (hAds : ∀ x, A (ds x) = Dimension.input hR hV q x)
    (hHb : H b0 = 0) (hAb : A b0 = []) (hHd : H drv = 0) (hAd : A drv = [])
    (hHl : H log = 0) (hAl : A log = [])
    (hother : ∀ y, mask y = true → (∀ x, ds x ≠ y) → y ≠ b0 →
      H y = 0 ∧ (A y).length ≤ Rc hR L C q)
    (hfit : q + 3 + prefixCost hR hV L C cVc q ≤ Rc hR L C q) :
    ∃ A' : Fin U → List Bool,
      Step (onceMachine hR hV L C cVc ds b0 drv log mask) (onceCost hR hV L C cVc q) H A H A' ∧
      A' drv = List.replicate (Rc hR L C q) true ∧
      A' log = List.replicate (Rc hR L C q + 2) false ∧
      (∀ y, mask y = true → A' y = List.replicate (Rc hR L C q) false) ∧
      A' (ds (pq hR hV)) = UnaryTemplate.tape q ∧
      A' (ds (pRl hR hV)) =
        List.replicate (C*(q+1)^hR*(2*2^(q - normalizedLiveCount q L)+3)+2) false ∧
      A' (ds (pV hR hV)) = List.replicate (cVc * RuntimeShape.tableClass L hV q) true ∧
      A' (ds (pVl hR hV)) =
        List.replicate (cVc*(q+1)^hV*(2*2^(q - normalizedLiveCount q L)+3)+2) false ∧
      (∀ y, mask y = false → (∀ x, ds x ≠ y) → y ≠ b0 → y ≠ drv → y ≠ log → A' y = A y) := by
  obtain ⟨W, hW, Wq, _, _, WR, WRl, WV, WVl, Wlen⟩ := Dimension.pipeline hR hV L C cVc q
  -- the pipeline, docked
  have s1 := hW.dock ds hds H A (fun x => hHds x) (fun x => hAds x)
  rw [BlockPlatform.dockH_existing ds H (fun _ => 0) (fun x => hHds x)] at s1
  let A1 := install ds A W
  have A1ds : ∀ x, A1 (ds x) = W x := fun x => install_slot ds hds A W x
  have A1off : ∀ y, (∀ x, ds x ≠ y) → A1 y = A y := fun y hy => install_other ds A W y hy
  -- the copier
  have hcs := copySlots_injective hR hV ds b0 drv log hb0 hdr hlg hbd hbl hdl
  let oC : Fin 4 → List Bool := ![List.replicate (Rc hR L C q) true, [],
    List.replicate (Rc hR L C q) true, List.replicate (Rc hR L C q + 2) false]
  have s2 := (BlockPlatform.UnaryCalc.copy_step (Rc hR L C q)).dock (copySlots hR hV ds b0 drv log)
    hcs H A1 (by
      intro j
      fin_cases j
      · exact hHds _
      · exact hHb
      · exact hHd
      · exact hHl) (by
      intro j
      fin_cases j
      · exact (A1ds _).trans WR
      · exact (A1off b0 hb0).trans hAb
      · exact (A1off drv hdr).trans hAd
      · exact (A1off log hlg).trans hAl)
  rw [BlockPlatform.dockH_existing _ H (fun _ => 0) (by
      intro j
      fin_cases j
      · exact hHds _
      · exact hHb
      · exact hHd
      · exact hHl)] at s2
  let A2 := install (copySlots hR hV ds b0 drv log) A1 oC
  have A2R : A2 (ds (pR hR hV)) = List.replicate (Rc hR L C q) true :=
    install_slot _ hcs A1 oC 0
  have A2b : A2 b0 = [] := install_slot _ hcs A1 oC 1
  have A2d : A2 drv = List.replicate (Rc hR L C q) true := install_slot _ hcs A1 oC 2
  have A2l : A2 log = List.replicate (Rc hR L C q + 2) false := install_slot _ hcs A1 oC 3
  have A2off : ∀ y, y ≠ ds (pR hR hV) → y ≠ b0 → y ≠ drv → y ≠ log → A2 y = A1 y := by
    intro y h0 h1 h2 h3
    refine install_other _ A1 oC y (fun j => ?_)
    fin_cases j
    · exact fun h => h0 h.symm
    · exact fun h => h1 h.symm
    · exact fun h => h2 h.symm
    · exact fun h => h3 h.symm
  -- the erase
  have hkeep : ∀ x, mask (ds x) = true → x ≠ pR hR hV → A2 (ds x) = W x := by
    intro x _ hx
    rw [A2off (ds x) (fun h => hx (hds h)) (hb0 x) (hdr x) (hlg x)]
    exact A1ds x
  have s3 := BlockPlatform.Scrub.erase_step mask drv log hmd hml hdl (Rc hR L C q)
    (Rc hR L C q + 2) (by omega) H A2 (by
      intro i hi
      rcases hi with hi | hi | hi
      · by_cases hx : ∃ x, ds x = i
        · obtain ⟨x, rfl⟩ := hx
          exact hHds x
        · by_cases hib : i = b0
          · rw [hib]; exact hHb
          · exact (hother i hi (fun x h => hx ⟨x, h⟩) hib).1
      · rw [hi]; exact hHd
      · rw [hi]; exact hHl) (by
      intro i hi
      by_cases hx : ∃ x, ds x = i
      · obtain ⟨x, rfl⟩ := hx
        by_cases hxR : x = pR hR hV
        · rw [hxR, A2R]; simp
        · have hq : x ≠ pq hR hV := fun h => by rw [h, hmq] at hi; exact absurd hi (by decide)
          have hRl : x ≠ pRl hR hV := fun h => by rw [h, hmRl] at hi; exact absurd hi (by decide)
          have hV' : x ≠ pV hR hV := fun h => by rw [h, hmV] at hi; exact absurd hi (by decide)
          have hVl : x ≠ pVl hR hV := fun h => by rw [h, hmVl] at hi; exact absurd hi (by decide)
          rw [hkeep x hi hxR]
          have := Wlen x hxR hRl hV' hVl
          omega
      · by_cases hib : i = b0
        · rw [hib, A2b]; simp
        · have hnd : i ≠ drv := fun h => by rw [h, hmd] at hi; exact absurd hi (by decide)
          have hnl : i ≠ log := fun h => by rw [h, hml] at hi; exact absurd hi (by decide)
          have hnR : i ≠ ds (pR hR hV) := fun h => hx ⟨_, h.symm⟩
          rw [A2off i hnR hib hnd hnl, A1off i (fun x h => hx ⟨x, h⟩)]
          exact (hother i hi (fun x h => hx ⟨x, h⟩) hib).2) A2d A2l
  refine ⟨BlockPlatform.Scrub.blank mask A2 (Rc hR L C q), (s1.seq s2).seq s3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [BlockPlatform.Scrub.blank, hmd, Bool.false_eq_true, if_false]; exact A2d
  · simp only [BlockPlatform.Scrub.blank, hml, Bool.false_eq_true, if_false]; exact A2l
  · intro y hy; simp only [BlockPlatform.Scrub.blank, hy, if_true]
  · have hne : pq hR hV ≠ pR hR hV := fun h => by
      have := congrArg Fin.val h; simp only [pq, pR, o1] at this; omega
    simp only [BlockPlatform.Scrub.blank, hmq, Bool.false_eq_true, if_false]
    rw [A2off _ (fun h => hne (hds h)) (hb0 _) (hdr _) (hlg _), A1ds]
    exact Wq
  · have hne : pRl hR hV ≠ pR hR hV := fun h => by
      have := congrArg Fin.val h; simp only [pRl, pR] at this; omega
    simp only [BlockPlatform.Scrub.blank, hmRl, Bool.false_eq_true, if_false]
    rw [A2off _ (fun h => hne (hds h)) (hb0 _) (hdr _) (hlg _), A1ds]
    exact WRl
  · have hne : pV hR hV ≠ pR hR hV := fun h => by
      have := congrArg Fin.val h; simp only [pV, pR, o2] at this; omega
    simp only [BlockPlatform.Scrub.blank, hmV, Bool.false_eq_true, if_false]
    rw [A2off _ (fun h => hne (hds h)) (hb0 _) (hdr _) (hlg _), A1ds]
    exact WV
  · have hne : pVl hR hV ≠ pR hR hV := fun h => by
      have := congrArg Fin.val h; simp only [pVl, pR, o2] at this; omega
    simp only [BlockPlatform.Scrub.blank, hmVl, Bool.false_eq_true, if_false]
    rw [A2off _ (fun h => hne (hds h)) (hb0 _) (hdr _) (hlg _), A1ds]
    exact WVl
  · intro y hy hyd hyb hydr hylg
    simp only [BlockPlatform.Scrub.blank, hy, Bool.false_eq_true, if_false]
    have hnR : y ≠ ds (pR hR hV) := fun h => hyd _ h.symm
    rw [A2off y hnR hyb hydr hylg, A1off y hyd]

/-- **Once, table class**: the producer, with its erase and copy, `≤ c·tableClass L (hR+1) q`. -/
theorem onceCost_class (L C cVc q : ℕ) (h2 : 2 ≤ hR) (hVR : hV + 1 ≤ hR) :
    onceCost hR hV L C cVc q ≤
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2 + 4*C + 12) *
        RuntimeShape.tableClass L (hR+1) q := by
  have hc := Dimension.cost_class hR hV L C cVc q h2 hVR
  have hm : Rc hR L C q ≤ C * RuntimeShape.tableClass L (hR+1) q :=
    Nat.mul_le_mul_left _ (RuntimeShape.tableClass_mono (by omega))
  have hone := SourceConstruction.one_le_tableClass L (hR+1) q
  unfold onceCost
  have e : (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2 + 4*C + 12) *
        RuntimeShape.tableClass L (hR+1) q =
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2) *
        RuntimeShape.tableClass L (hR+1) q + 4*(C * RuntimeShape.tableClass L (hR+1) q) +
        12 * RuntimeShape.tableClass L (hR+1) q := by ring
  rw [e]
  omega

end
end NearCubicWires.SourceConstruction.Once
end
