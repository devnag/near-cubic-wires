import Proof.Packets.SrcMetaRun
import Proof.SourceAssembly.SourceSkelInitXA

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceStart.MetaStep
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission
open NearCubicWires.SourceStart.MetaProg NearCubicWires.SourceStart.MetaRun
open NearCubicWires.SourceSkeleton.InitS (InitInv MetaRun stripT extF extF_val eb sb slotVal slotVal_some slotVal_none
  fixedOf ResExt pad_frame_ones)
noncomputable section

/-! ## 1. The degenerate-case flags -/

/-- `cc0 = 0` (then `mC q = 0` for every `q`). -/
def czOf (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) : Bool :=
  decide (cc0 selector (decompositionOf s) p.clauseDegree (tgt s p) = 0)

/-- `v0C = 0` (then `mV q = 0` for every `q`). -/
def vzOf (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) : Bool :=
  decide (v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) = 0)

theorem czOf_iff (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) :
    czOf selector s p = true ↔ Meta.mC selector s p q = 0 := by
  unfold czOf Meta.mC
  simp [Nat.mul_eq_zero, pow_eq_zero_iff']

theorem vzOf_iff (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) :
    vzOf selector s p = true ↔ Meta.mV selector s p q = 0 := by
  unfold vzOf Meta.mV
  simp [Nat.mul_eq_zero, pow_eq_zero_iff']

variable {selector : CyclicChoice.Laws} {s : EightSources} {gamma : Real} {p : Parameters s gamma}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector} {L : ℕ}

/-- **The meta stage's cost.** -/
def metaCost (V : Meta.MetaVals2 selector s p packets L) (q : ℕ) : ℕ :=
  progCost V (czOf selector s p) (vzOf selector s p) q

/-! ## 2. The dock -/

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-- The slot map: four locals onto `rsT 4` and strip slots `15, 17, 18`; local `i` otherwise onto extension tape `u + i`. -/
def gsl (V : Meta.MetaVals2 selector s p packets L) (u : ℕ) (i : Fin (191 + V.NP)) : Fin T :=
  if i.val = 0 then Dims.rsT pl.ext.rest pl.hT 4
  else if i.val = 1 then stripT pl hh 15 (by decide)
  else if i.val = 13 then stripT pl hh 17 (by decide)
  else if i.val = 14 then stripT pl hh 18 (by decide)
  else extF (NS := NS) pl (u + i.val)

/-- **The meta stage** (ONE fixed machine on the site universe). -/
def metaM (V : Meta.MetaVals2 selector s p packets L) (u : ℕ) :=
  RecoveryFocus.machine (gsl pl hh V u) (progM V (czOf selector s p) (vzOf selector s p))

theorem gsl_val {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (V : Meta.MetaVals2 selector s p packets L) (u : ℕ)
    (hu : u + (191 + V.NP) ≤ NE) (i : Fin (191 + V.NP)) :
    (gsl pl hh V u i).val = if i.val = 0 then d.B + 19 + restPc eX pX gW + 4
      else if i.val = 1 then sb d eX pX gW + 15 else if i.val = 13 then sb d eX pX gW + 17
      else if i.val = 14 then sb d eX pX gW + 18 else eb d eX pX gW X NS + (u + i.val) := by
  unfold gsl
  by_cases c0 : i.val = 0
  · rw [if_pos c0, if_pos c0]; rfl
  · rw [if_neg c0, if_neg c0]
    by_cases c1 : i.val = 1
    · rw [if_pos c1, if_pos c1]; rfl
    · rw [if_neg c1, if_neg c1]
      by_cases c13 : i.val = 13
      · rw [if_pos c13, if_pos c13]; rfl
      · rw [if_neg c13, if_neg c13]
        by_cases c14 : i.val = 14
        · rw [if_pos c14, if_pos c14]; rfl
        · rw [if_neg c14, if_neg c14]
          exact extF_val pl hE _ (by have := i.isLt; omega)

theorem gsl_inj {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (V : Meta.MetaVals2 selector s p packets L) (u : ℕ)
    (hu : u + (191 + V.NP) ≤ NE) : Function.Injective (gsl pl hh V u) := by
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  have hr4 : d.B + 19 + restPc eX pX gW + 4 < sb d eX pX gW := by unfold sb; omega
  -- a left inverse on values
  let back : ℕ → ℕ := fun v =>
    if v = d.B + 19 + restPc eX pX gW + 4 then 0 else if v = sb d eX pX gW + 15 then 1
    else if v = sb d eX pX gW + 17 then 13 else if v = sb d eX pX gW + 18 then 14 else v - eb d eX pX gW X NS - u
  have hb : ∀ i : Fin (191 + V.NP), back (gsl pl hh V u i).val = i.val := by
    intro i
    rw [gsl_val pl hh hE V u hu i]
    by_cases c0 : i.val = 0
    · rw [if_pos c0]; simp only [back, if_pos rfl]; exact c0.symm
    · rw [if_neg c0]
      by_cases c1 : i.val = 1
      · rw [if_pos c1]
        simp only [back, if_neg (show sb d eX pX gW + 15 ≠ d.B + 19 + restPc eX pX gW + 4 by omega), if_pos rfl]
        exact c1.symm
      · rw [if_neg c1]
        by_cases c13 : i.val = 13
        · rw [if_pos c13]
          simp only [back, if_neg (show sb d eX pX gW + 17 ≠ d.B + 19 + restPc eX pX gW + 4 by omega),
            if_neg (show sb d eX pX gW + 17 ≠ sb d eX pX gW + 15 by omega), if_pos rfl]
          exact c13.symm
        · rw [if_neg c13]
          by_cases c14 : i.val = 14
          · rw [if_pos c14]
            simp only [back, if_neg (show sb d eX pX gW + 18 ≠ d.B + 19 + restPc eX pX gW + 4 by omega),
              if_neg (show sb d eX pX gW + 18 ≠ sb d eX pX gW + 15 by omega),
              if_neg (show sb d eX pX gW + 18 ≠ sb d eX pX gW + 17 by omega), if_pos rfl]
            exact c14.symm
          · rw [if_neg c14]
            have n1 : eb d eX pX gW X NS + (u + i.val) ≠ d.B + 19 + restPc eX pX gW + 4 := by omega
            have n2 : eb d eX pX gW X NS + (u + i.val) ≠ sb d eX pX gW + 15 := by omega
            have n3 : eb d eX pX gW X NS + (u + i.val) ≠ sb d eX pX gW + 17 := by omega
            have n4 : eb d eX pX gW X NS + (u + i.val) ≠ sb d eX pX gW + 18 := by omega
            simp only [back, if_neg n1, if_neg n2, if_neg n3, if_neg n4]
            omega
  intro i j h
  apply Fin.ext
  rw [← hb i, ← hb j, h]

/-! ## 3. The contract -/

theorem meta_step {NR NE : Nat} (hNR19 : 19 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    (V : Meta.MetaVals2 selector s p packets L) {cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    (u : ℕ) (hu : u + (191 + V.NP) ≤ NE) (hR : 1 ≤ Rc)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Rc) (hK : 2 * normalizedLiveCount q L + 1 ≤ Rc) :
    MetaRun pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg (MBof selector s p packets L q) u
      (metaM pl hh V u) (metaCost V q) (191 + V.NP) := by
  refine ⟨hu, ?_⟩
  intro val H H' A A' hinv _ h15 _ h17 h18
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  have hr4 : d.B + 19 + restPc eX pX gW + 4 < sb d eX pX gW := by unfold sb; omega
  have vs : ∀ j hj, (stripT pl hh j hj).val = sb d eX pX gW + j := fun _ _ => rfl
  have gv := gsl_val pl hh hE V u hu
  have ginj := gsl_inj pl hh hE V u hu
  obtain ⟨_, ⟨q4A, q4H⟩⟩ := fixedOf pl hh hinv
  -- the strip slots read
  have strip_at : ∀ i (hi : i < 32), 8 ≤ i → i < NR →
      A' (stripT pl hh i hi) = slotVal Rc val i ∧ H' (stripT pl hh i hi) = 0 := by
    intro i hi h8 hN
    have := hinv.strip (stripT pl hh i hi) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + i - sb d eX pX gW = i by omega] at this
    exact this
  have s15o := strip_at 15 (by decide) (by decide) (by omega)
  have s15 := s15o
  have s17 := strip_at 17 (by decide) (by decide) (by omega)
  have s18 := strip_at 18 (by decide) (by decide) (by omega)
  rw [slotVal_some Rc val 15 _ h15, pad_frame_ones Rc _ hK] at s15
  rw [slotVal_none Rc val 17 h17] at s17
  rw [slotVal_none Rc val 18 h18] at s18
  -- the local entry
  set Eloc : Fin (191 + V.NP) → List Bool := fun i => A' (gsl pl hh V u i) with hEloc
  have ext_at : ∀ i : Fin (191 + V.NP), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 13 → i.val ≠ 14 →
      (gsl pl hh V u i).val = eb d eX pX gW X NS + (u + i.val) := by
    intro i c0 c1 c13 c14
    rw [gv i, if_neg c0, if_neg c1, if_neg c13, if_neg c14]
  have loc : ∀ i : Fin (191 + V.NP), H' (gsl pl hh V u i) = 0 ∧
      (2 ≤ i.val → A' (gsl pl hh V u i) = List.replicate Rc false) := by
    intro i
    by_cases c0 : i.val = 0
    · have e : gsl pl hh V u i = Dims.rsT pl.ext.rest pl.hT 4 := by unfold gsl; rw [if_pos c0]
      rw [e]; exact ⟨q4H, fun h => absurd c0 (by omega)⟩
    · by_cases c1 : i.val = 1
      · have e : gsl pl hh V u i = stripT pl hh 15 (by decide) := by unfold gsl; rw [if_neg c0, if_pos c1]
        rw [e]; exact ⟨s15.2, fun h => absurd c1 (by omega)⟩
      · by_cases c13 : i.val = 13
        · have e : gsl pl hh V u i = stripT pl hh 17 (by decide) := by unfold gsl; rw [if_neg c0, if_neg c1, if_pos c13]
          rw [e]; exact ⟨s17.2, fun _ => s17.1⟩
        · by_cases c14 : i.val = 14
          · have e : gsl pl hh V u i = stripT pl hh 18 (by decide) := by
              unfold gsl; rw [if_neg c0, if_neg c1, if_neg c13, if_pos c14]
            rw [e]; exact ⟨s18.2, fun _ => s18.1⟩
          · have ev := ext_at i c0 c1 c13 c14
            have fr := hinv.fresh (gsl pl hh V u i) (by rw [ev]; omega) (by rw [ev]; have := i.isLt; omega)
            exact ⟨fr.2, fun _ => fr.1⟩
  have e0 : gsl pl hh V u (rg V 0) = Dims.rsT pl.ext.rest pl.hT 4 := by unfold gsl; rfl
  have e1 : gsl pl hh V u (rg V 1) = stripT pl hh 15 (by decide) := by unfold gsl; rfl
  have e13 : gsl pl hh V u (rg V 13) = stripT pl hh 17 (by decide) := by unfold gsl; rfl
  have e14 : gsl pl hh V u (rg V 14) = stripT pl hh 18 (by decide) := by unfold gsl; rfl
  obtain ⟨E', hrun, o0, o1, o13, o14⟩ := prog_run V (czOf selector s p) (vzOf selector s p) q Rc hR hcap
    (czOf_iff selector s p q) (vzOf_iff selector s p q) Eloc (by show A' _ = _; rw [e0]; exact q4A)
    (by show A' _ = _; rw [e1]; exact s15.1) (fun x hx => (loc x).2 hx)
  have dk := hrun.dock (gsl pl hh V u) ginj H' A' (fun j => (loc j).1) (fun _ => rfl)
  rw [dockH_existing (gsl pl hh V u) H' _ (fun j => (loc j).1)] at dk
  set A'' := install (gsl pl hh V u) A' E' with hA''
  refine ⟨A'', dk, ?_⟩
  -- the image of the dock
  have img : ∀ x : Fin T, (∀ j, gsl pl hh V u j ≠ x) → A'' x = A' x := fun x hx => install_other _ _ _ _ hx
  have at_ : ∀ j, A'' (gsl pl hh V u j) = E' j := fun j => install_slot _ ginj _ _ j
  refine NearCubicWires.SourceSkeleton.InitS.step pl hh hNR hinv A'' _ (u + (191 + V.NP)) (by omega) hu ?_ ?_ ?_
  · -- off the strip and the used block: only `rsT 4` is in the image, and it is returned
    intro x h1 h2
    by_cases cx : x = Dims.rsT pl.ext.rest pl.hT 4
    · rw [cx, ← e0, at_, o0]
    · apply img
      intro j hj
      rw [← hj] at h1 h2 cx
      by_cases c0 : j.val = 0
      · exact cx (by unfold gsl; rw [if_pos c0])
      · by_cases c1 : j.val = 1
        · exact h1 ⟨by rw [gv j, if_neg c0, if_pos c1]; omega, by rw [gv j, if_neg c0, if_pos c1]; omega⟩
        · by_cases c13 : j.val = 13
          · exact h1 ⟨by rw [gv j, if_neg c0, if_neg c1, if_pos c13]; omega,
              by rw [gv j, if_neg c0, if_neg c1, if_pos c13]; omega⟩
          · by_cases c14 : j.val = 14
            · exact h1 ⟨by rw [gv j, if_neg c0, if_neg c1, if_neg c13, if_pos c14]; omega,
                by rw [gv j, if_neg c0, if_neg c1, if_neg c13, if_pos c14]; omega⟩
            · have ev := ext_at j c0 c1 c13 c14
              exact h2 ⟨by rw [ev]; omega, by rw [ev]; have := j.isLt; omega⟩
  · -- the strip
    intro x h1 h2
    by_cases c15 : x.val = sb d eX pX gW + 15
    · have ex : x = stripT pl hh 15 (by decide) := Fin.ext (by rw [vs]; exact c15)
      rw [ex, ← e1, at_, o1]
      show A' (gsl pl hh V u (rg V 1)) = _
      rw [e1, s15o.1, vs, show sb d eX pX gW + 15 - sb d eX pX gW = 15 by omega]
      simp only [slotVal, if_neg (show (15:ℕ) ≠ 17 by decide), if_neg (show (15:ℕ) ≠ 18 by decide)]
    · by_cases c17 : x.val = sb d eX pX gW + 17
      · have ex : x = stripT pl hh 17 (by decide) := Fin.ext (by rw [vs]; exact c17)
        have a17 : A'' (stripT pl hh 17 (by decide)) = ZeroPadding.pad Rc (RepairOrdinary.frame (MBof selector s p packets L q)) := by
          rw [← e13, at_, o13]
        rw [ex, a17, vs, show sb d eX pX gW + 17 - sb d eX pX gW = 17 by omega]
        simp [slotVal]
      · by_cases c18 : x.val = sb d eX pX gW + 18
        · have ex : x = stripT pl hh 18 (by decide) := Fin.ext (by rw [vs]; exact c18)
          have a18 : A'' (stripT pl hh 18 (by decide)) =
              ZeroPadding.pad Rc (RepairOrdinary.frame (List.replicate (MBof selector s p packets L q).length true)) := by
            rw [← e14, at_, o14]
          rw [ex, a18, vs, show sb d eX pX gW + 18 - sb d eX pX gW = 18 by omega]
          simp [slotVal]
        · rw [img x ?_, (hinv.strip x h1 h2).1]
          · have a17 : x.val - sb d eX pX gW ≠ 17 := by omega
            have a18 : x.val - sb d eX pX gW ≠ 18 := by omega
            simp only [slotVal, if_neg a17, if_neg a18]
          · intro j hj
            rw [← hj] at c15 c17 c18 h1 h2
            by_cases c0 : j.val = 0
            · rw [gv j, if_pos c0] at h1; omega
            · by_cases c1 : j.val = 1
              · exact c15 (by rw [gv j, if_neg c0, if_pos c1])
              · by_cases c13 : j.val = 13
                · exact c17 (by rw [gv j, if_neg c0, if_neg c1, if_pos c13])
                · by_cases c14 : j.val = 14
                  · exact c18 (by rw [gv j, if_neg c0, if_neg c1, if_neg c13, if_pos c14])
                  · have ev := ext_at j c0 c1 c13 c14
                    rw [ev] at h2; omega
  · -- the used block: no tape shortens
    intro x h1 h2
    have fr := hinv.fresh x (by omega) (by omega)
    have hl : (A' x).length ≤ (A'' x).length := by
      by_cases cx : ∃ j, gsl pl hh V u j = x
      · obtain ⟨j, rfl⟩ := cx
        rw [at_]
        exact CloseoutFinalC10WorkerEmitShape.Step_length_le hrun j
      · rw [img x (fun j hj => cx ⟨j, hj⟩)]
    rw [fr.1, List.length_replicate] at hl
    exact hl

end
end NearCubicWires.SourceStart.MetaStep

