import Proof.SourceAssembly.SourceRequestSelRunThr
import Proof.SourceAssembly.SourceRestIn4

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.SourceConstruction
noncomputable section

/-! ## The high offsets and their inverse (injectivity without per-case arithmetic loops) -/

/-- The offset above `B` of a non-low local port (`x = eX + pX`, `Pc = restPc eX pX gW`). -/
def hv (Pc x z : Nat) : Nat :=
  if z = 20 then 83 else if z < 31 then 29 + Pc + (z - 21) else if z = 31 then 41 + Pc else if z = 33 then 89
  else if z < 37 then 80 + (z - 34) else if z = 39 then 48 + Pc else 90 + x + z

/-- Its left inverse on the high ports. -/
def hvinv (Pc x v : Nat) : Nat :=
  if v = 83 then 20 else if v = 89 then 33 else if v < 90 then 34 + (v - 80) else if v < 19 + Pc then v - (90 + x)
  else if v < 39 + Pc then 21 + (v - (29 + Pc)) else if v = 41 + Pc then 31 else 39

/-- A local port is LOW when it lands below `F` (cache, witness, terminal). -/
def Low (z : Nat) : Prop := z < 19 ∨ z = 19 ∨ z = 32

theorem hvinv_hv (x gW z : Nat) (hz : ¬ Low z) (hzg : z < gW) :
    hvinv (71 + x + gW) x (hv (71 + x + gW) x z) = z := by
  unfold Low at hz
  by_cases h20 : z = 20
  · subst h20; simp [hv, hvinv]
  have h19 : 20 < z ∨ z < 19 := by omega
  by_cases h31 : z < 31
  · have hv' : hv (71 + x + gW) x z = 29 + (71 + x + gW) + (z - 21) := by simp only [hv, if_neg h20, if_pos h31]
    rw [hv']
    have a1 : 29 + (71 + x + gW) + (z - 21) ≠ 83 := by omega
    have a2 : 29 + (71 + x + gW) + (z - 21) ≠ 89 := by omega
    have a3 : ¬ 29 + (71 + x + gW) + (z - 21) < 90 := by omega
    have a4 : ¬ 29 + (71 + x + gW) + (z - 21) < 19 + (71 + x + gW) := by omega
    have a5 : 29 + (71 + x + gW) + (z - 21) < 39 + (71 + x + gW) := by omega
    simp only [hvinv, if_neg a1, if_neg a2, if_neg a3, if_neg a4, if_pos a5]
    omega
  by_cases h31' : z = 31
  · subst h31'
    have hv' : hv (71 + x + gW) x 31 = 41 + (71 + x + gW) := by simp [hv]
    rw [hv']
    have a1 : 41 + (71 + x + gW) ≠ 83 := by omega
    have a2 : 41 + (71 + x + gW) ≠ 89 := by omega
    have a3 : ¬ 41 + (71 + x + gW) < 90 := by omega
    have a4 : ¬ 41 + (71 + x + gW) < 19 + (71 + x + gW) := by omega
    have a5 : ¬ 41 + (71 + x + gW) < 39 + (71 + x + gW) := by omega
    simp only [hvinv, if_neg a1, if_neg a2, if_neg a3, if_neg a4, if_neg a5]; simp
  by_cases h33 : z = 33
  · subst h33; simp [hv, hvinv]
  by_cases h37 : z < 37
  · have hz3 : 34 ≤ z := by omega
    have hv' : hv (71 + x + gW) x z = 80 + (z - 34) := by
      simp only [hv, if_neg h20, if_neg h31, if_neg h31', if_neg h33, if_pos h37]
    rw [hv']
    have a1 : 80 + (z - 34) ≠ 83 := by omega
    have a2 : 80 + (z - 34) ≠ 89 := by omega
    have a3 : 80 + (z - 34) < 90 := by omega
    simp only [hvinv, if_neg a1, if_neg a2, if_pos a3]
    omega
  by_cases h39 : z = 39
  · subst h39
    have hv' : hv (71 + x + gW) x 39 = 48 + (71 + x + gW) := by simp [hv]
    rw [hv']
    have a1 : 48 + (71 + x + gW) ≠ 83 := by omega
    have a2 : 48 + (71 + x + gW) ≠ 89 := by omega
    have a3 : ¬ 48 + (71 + x + gW) < 90 := by omega
    have a4 : ¬ 48 + (71 + x + gW) < 19 + (71 + x + gW) := by omega
    have a5 : ¬ 48 + (71 + x + gW) < 39 + (71 + x + gW) := by omega
    have a6 : 48 + (71 + x + gW) ≠ 41 + (71 + x + gW) := by omega
    simp only [hvinv, if_neg a1, if_neg a2, if_neg a3, if_neg a4, if_neg a5, if_neg a6]
  · have hv' : hv (71 + x + gW) x z = 90 + x + z := by
      simp only [hv, if_neg h20, if_neg h31, if_neg h31', if_neg h33, if_neg h37, if_neg h39]
    rw [hv']
    have a1 : 90 + x + z ≠ 83 := by omega
    have a2 : 90 + x + z ≠ 89 := by omega
    have a3 : ¬ 90 + x + z < 90 := by omega
    have a4 : 90 + x + z < 19 + (71 + x + gW) := by omega
    simp only [hvinv, if_neg a1, if_neg a2, if_neg a3, if_pos a4]
    omega

/-- Every high offset lies below the high residents' end `49 + Pc`, and region offsets lie in `[90 + x, 19 + Pc)`. -/
theorem hv_lt (x gW z : Nat) (hz : ¬ Low z) (hzg : z < gW) : hv (71 + x + gW) x z < 49 + (71 + x + gW) := by
  unfold Low at hz
  unfold hv
  by_cases h20 : z = 20
  · rw [if_pos h20]; omega
  rw [if_neg h20]
  by_cases h31 : z < 31
  · rw [if_pos h31]; omega
  rw [if_neg h31]
  by_cases h31' : z = 31
  · rw [if_pos h31']; omega
  rw [if_neg h31']
  by_cases h33 : z = 33
  · rw [if_pos h33]; omega
  rw [if_neg h33]
  by_cases h37 : z < 37
  · rw [if_pos h37]; omega
  rw [if_neg h37]
  by_cases h39 : z = 39
  · rw [if_pos h39]; omega
  rw [if_neg h39]; omega

section dock
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

theorem B_lt_U (hV : d.U ≤ V) (i : Nat) (hi : i < d.res) : d.B + i < V := by
  have h : d.B + i < d.U := by
    unfold SourceConstruction.Dims.B SourceConstruction.Dims.U SourceConstruction.Dims.G SourceConstruction.Dims.prepT
    omega
  exact Nat.lt_of_lt_of_le h hV

theorem one_lt_V (e : d.RestExt3 eX pX gW) (hV : d.U ≤ V) : 1 < V := by
  have hF := e.ext2.ext1.ext.hF
  have h : 1 < d.U := by
    unfold SourceConstruction.Dims.U SourceConstruction.Dims.G SourceConstruction.Dims.prepT
    omega
  exact Nat.lt_of_lt_of_le h hV

def gS (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
    (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tT da) ≤ gW)
    (z : Fin (NF + (19 + 4 * tT da))) : Fin V :=
  if h : z.val < 19 then cacheT ⟨z.val, h⟩
  else if h19 : z.val = 19 then ⟨1, one_lt_V e hV⟩
  else if h32 : z.val = 32 then terminal
  else ⟨d.B + hv (restPc eX pX gW) (eX + pX) z.val, B_lt_U hV _ (by
    have e1 : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
    have := hv_lt (eX + pX) gW z.val (by unfold Low; omega) (Nat.lt_of_lt_of_le z.isLt hN)
    rw [e1] at hres ⊢; omega)⟩

variable (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tT da) ≤ gW)

theorem gS_high (z : Fin (NF + (19 + 4 * tT da))) (hz : ¬ Low z.val) :
    (gS e hV da cacheT terminal hres hN z).val = d.B + hv (restPc eX pX gW) (eX + pX) z.val := by
  unfold Low at hz
  unfold gS
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

theorem gS_cache (j : Fin 19) :
    gS e hV da cacheT terminal hres hN (up ⟨j.val, by have := j.isLt; unfold NF; omega⟩) = cacheT j := by
  unfold gS
  rw [dif_pos (show (up (t := tT da) ⟨j.val, _⟩).val < 19 from j.isLt)]
  rfl

theorem gS_wit : (gS e hV da cacheT terminal hres hN (up 19)).val = 1 := rfl

theorem gS_term : gS e hV da cacheT terminal hres hN (up 32) = terminal := rfl

/-- **The dock is injective** (S's low tapes distinct from each other; everything else by offset). -/
theorem gS_inj (hci : Function.Injective cacheT) (hcF : ∀ j, (cacheT j).val < d.F) (htF : terminal.val < d.F)
    (hc1 : ∀ j, (cacheT j).val ≠ 1) (hct : ∀ j, cacheT j ≠ terminal) (ht1 : terminal.val ≠ 1) :
    Function.Injective (gS e hV da cacheT terminal hres hN) := by
  have hFB : d.F ≤ d.B := by
    unfold SourceConstruction.Dims.B SourceConstruction.Dims.G; omega
  have h1F : 1 < d.F := by have := e.ext2.ext1.ext.hF; omega
  -- a low port's value is below F; a high port's is at least B
  have lowv : ∀ z : Fin (NF + (19 + 4 * tT da)), Low z.val → (gS e hV da cacheT terminal hres hN z).val < d.F := by
    intro z hz
    unfold gS
    by_cases h19 : z.val < 19
    · rw [dif_pos h19]; exact hcF _
    · rw [dif_neg h19]
      by_cases h19' : z.val = 19
      · rw [dif_pos h19']; exact h1F
      · rw [dif_neg h19', dif_pos (by unfold Low at hz; omega)]; exact htF
  intro a b hab
  have hv' := congrArg Fin.val hab
  by_cases la : Low a.val
  · by_cases lb : Low b.val
    · -- both low
      unfold Low at la lb
      unfold gS at hab
      by_cases a19 : a.val < 19
      · by_cases b19 : b.val < 19
        · rw [dif_pos a19, dif_pos b19] at hab
          have h2 := congrArg Fin.val (hci hab)
          exact Fin.ext h2
        · rw [dif_pos a19, dif_neg b19] at hab
          by_cases b19' : b.val = 19
          · rw [dif_pos b19'] at hab; exact absurd (congrArg Fin.val hab) (hc1 _)
          · rw [dif_neg b19', dif_pos (by omega)] at hab; exact absurd hab (hct _)
      · rw [dif_neg a19] at hab
        by_cases a19' : a.val = 19
        · rw [dif_pos a19'] at hab
          by_cases b19 : b.val < 19
          · rw [dif_pos b19] at hab; exact absurd (congrArg Fin.val hab).symm (hc1 _)
          · rw [dif_neg b19] at hab
            by_cases b19' : b.val = 19
            · exact Fin.ext (a19'.trans b19'.symm)
            · rw [dif_neg b19', dif_pos (by omega)] at hab; exact absurd (congrArg Fin.val hab).symm ht1
        · rw [dif_neg a19', dif_pos (by omega)] at hab
          by_cases b19 : b.val < 19
          · rw [dif_pos b19] at hab; exact absurd hab.symm (hct _)
          · rw [dif_neg b19] at hab
            by_cases b19' : b.val = 19
            · rw [dif_pos b19'] at hab; exact absurd (congrArg Fin.val hab) ht1
            · exact Fin.ext (by omega)
    · have h1 := lowv a la
      rw [hv', gS_high e hV da cacheT terminal hres hN b lb] at h1
      omega
  · by_cases lb : Low b.val
    · have h1 := lowv b lb
      rw [← hv', gS_high e hV da cacheT terminal hres hN a la] at h1
      omega
    · rw [gS_high e hV da cacheT terminal hres hN a la, gS_high e hV da cacheT terminal hres hN b lb] at hv'
      have hh : hv (restPc eX pX gW) (eX + pX) a.val = hv (restPc eX pX gW) (eX + pX) b.val := by omega
      have ia := hvinv_hv (eX + pX) gW a.val la (by have := a.isLt; omega)
      have ib := hvinv_hv (eX + pX) gW b.val lb (by have := b.isLt; omega)
      have e1 : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
      rw [e1] at hh
      rw [hh] at ia
      exact Fin.ext (ia.symm.trans ib)

end dock

/-! ## The ports: offsets of the named local ports -/

theorem hv_20 (Pc x : Nat) : hv Pc x 20 = 83 := by simp [hv]
theorem hv_21 (Pc x i : Nat) (hi : i < 10) : hv Pc x (21 + i) = 29 + Pc + i := by
  have h1 : 21 + i ≠ 20 := by omega
  have h2 : 21 + i < 31 := by omega
  simp only [hv, if_neg h1, if_pos h2]
  omega
theorem hv_31 (Pc x : Nat) : hv Pc x 31 = 41 + Pc := by simp [hv]
theorem hv_33 (Pc x : Nat) : hv Pc x 33 = 89 := by simp [hv]
theorem hv_34 (Pc x i : Nat) (hi : i < 3) : hv Pc x (34 + i) = 80 + i := by
  have h1 : 34 + i ≠ 20 := by omega
  have h2 : ¬ 34 + i < 31 := by omega
  have h3 : 34 + i ≠ 31 := by omega
  have h4 : 34 + i ≠ 33 := by omega
  have h5 : 34 + i < 37 := by omega
  simp only [hv, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
  omega
theorem hv_39 (Pc x : Nat) : hv Pc x 39 = 48 + Pc := by simp [hv]
theorem hv_reg (Pc x z : Nat) (h37 : 37 ≤ z) (h39 : z ≠ 39) : hv Pc x z = 90 + x + z := by
  have h1 : z ≠ 20 := by omega
  have h2 : ¬ z < 31 := by omega
  have h3 : z ≠ 31 := by omega
  have h4 : z ≠ 33 := by omega
  have h5 : ¬ z < 37 := by omega
  simp only [hv, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h39]

def resW (q Pw W Ld L target cwid cw i : Nat) : List Bool :=
  if i = 0 then UnaryTemplate.tape q else if i = 1 then List.replicate Pw true
  else if i = 2 then List.replicate W true else if i = 3 then List.replicate Ld true
  else if h : i < 8 then RepairOrdinary.frame (SourceFactorSel.Header.fields false q L target 0 ⟨i - 4, by omega⟩)
  else if i = 8 then List.replicate cwid true else List.replicate cw true

section S
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
  (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tT da) ≤ gW)

theorem gS_out (z : Fin (NF + (19 + 4 * tT da))) (h33 : 33 ≤ z.val) (h39 : z.val ≠ 39) :
    Rest.OutV d eX pX gW (gS e hV da cacheT terminal hres hN z).val := by
  have hl : ¬ Low z.val := by unfold Low; omega
  rw [gS_high e hV da cacheT terminal hres hN z hl]
  unfold Rest.OutV
  by_cases e33 : z.val = 33
  · rw [e33, hv_33]; right; right; right; left; omega
  by_cases h37 : z.val < 37
  · have ez : z.val = 34 + (z.val - 34) := by omega
    rw [ez, hv_34 _ _ _ (by omega)]
    right; right; left; omega
  · rw [hv_reg _ _ _ (by omega) h39]
    have hz := Nat.lt_of_lt_of_le z.isLt hN
    right; right; right; right
    unfold restPc; omega

end S

section SelRunS
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
  (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tT da) ≤ gW)

theorem gS_nT : gS e hV da cacheT terminal hres hN (up 33) = Dims.pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩ :=
  Fin.ext (by
    rw [gS_high e hV da cacheT terminal hres hN _ (by unfold Low; show ¬ (33 < 19 ∨ 33 = 19 ∨ 33 = 32); decide), up_val]
    show d.B + hv _ _ 33 = d.B + 19 + 70
    rw [hv_33])

theorem gS_coefT (i : Fin 3) :
    gS e hV da cacheT terminal hres hN (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) =
      Dims.pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩ :=
  Fin.ext (by
    have hi := i.isLt
    rw [gS_high e hV da cacheT terminal hres hN _ (by unfold Low; show ¬ (34 + i.val < 19 ∨ 34 + i.val = 19 ∨ 34 + i.val = 32); omega),
      up_val]
    show d.B + hv _ _ (34 + i.val) = d.B + 19 + (61 + i.val)
    rw [hv_34 _ _ _ hi]; omega)

theorem gS_regR (Pw W Ld gG7 : Nat) (hG : NF + (19 + 4 * tT da) ≤ gG7) {n0 : Nat} {circuit : BooleanCircuit n0}
    (pcpp : PointwisePCPP circuit) (x : Fin (19 + 4 * (PT (pcpp := pcpp) da Pw W Ld).t)) :
    d.B + 90 + eX + pX ≤ (gS e hV da cacheT terminal hres hN (rgP (PT (pcpp := pcpp) da Pw W Ld) x)).val ∧
      (gS e hV da cacheT terminal hres hN (rgP (PT (pcpp := pcpp) da Pw W Ld) x)).val < d.B + 90 + eX + pX + gG7 := by
  have hx : x.val < 19 + 4 * tT da := x.isLt
  have hz : ¬ Low (NF + x.val) := by unfold Low NF; omega
  have e1 := gS_high e hV da cacheT terminal hres hN (rgP (PT (pcpp := pcpp) da Pw W Ld) x) hz
  rw [e1, rg_val, hv_reg _ _ _ (by unfold NF; omega) (by unfold NF; omega)]
  exact ⟨by omega, by unfold NF at *; omega⟩

theorem gS_scr (gG7 : Nat) (hG : NF + (19 + 4 * tT da) ≤ gG7) (x : Fin V)
    (hx : ∃ z : Fin NF, 100 ≤ z.val ∧ gS e hV da cacheT terminal hres hN (up z) = x) :
    d.B + 90 + eX + pX ≤ x.val ∧ x.val < d.B + 90 + eX + pX + gG7 := by
  obtain ⟨z, hz1, rfl⟩ := hx
  have hzl : z.val < NF := z.isLt
  have hz : ¬ Low z.val := by unfold Low; omega
  have e1 := gS_high e hV da cacheT terminal hres hN (up z) hz
  rw [up_val] at e1
  rw [e1, hv_reg _ _ _ (by omega) (by omega)]
  exact ⟨by omega, by unfold NF at *; omega⟩

end SelRunS

end
end NearCubicWires.SourceRequest.SelLocal

