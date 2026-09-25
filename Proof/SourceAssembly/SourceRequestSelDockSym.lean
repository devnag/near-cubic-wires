import Proof.SourceAssembly.SourceRequestSelDockS
import Proof.SourceAssembly.SourceRequestSelSymRun

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

section dockSym
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

def gSS (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
    (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tS) ≤ gW)
    (z : Fin (NF + (19 + 4 * tS))) : Fin V :=
  if h : z.val < 19 then cacheT ⟨z.val, h⟩
  else if h19 : z.val = 19 then ⟨1, one_lt_V e hV⟩
  else if h32 : z.val = 32 then terminal
  else ⟨d.B + hv (restPc eX pX gW) (eX + pX) z.val, B_lt_U hV _ (by
    have e1 : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
    have := hv_lt (eX + pX) gW z.val (by unfold Low; omega) (Nat.lt_of_lt_of_le z.isLt hN)
    rw [e1] at hres ⊢; omega)⟩

variable (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tS) ≤ gW)

theorem gSS_high (z : Fin (NF + (19 + 4 * tS))) (hz : ¬ Low z.val) :
    (gSS e hV da cacheT terminal hres hN z).val = d.B + hv (restPc eX pX gW) (eX + pX) z.val := by
  unfold Low at hz
  unfold gSS
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

theorem gSS_cache (j : Fin 19) :
    gSS e hV da cacheT terminal hres hN (up ⟨j.val, by have := j.isLt; unfold NF; omega⟩) = cacheT j := by
  unfold gSS
  rw [dif_pos (show (up (t := tS) ⟨j.val, _⟩).val < 19 from j.isLt)]
  rfl

theorem gSS_wit : (gSS e hV da cacheT terminal hres hN (up 19)).val = 1 := rfl

theorem gSS_term : gSS e hV da cacheT terminal hres hN (up 32) = terminal := rfl

/-- **The dock is injective** (S's low tapes distinct from each other; everything else by offset). -/
theorem gSS_inj (hci : Function.Injective cacheT) (hcF : ∀ j, (cacheT j).val < d.F) (htF : terminal.val < d.F)
    (hc1 : ∀ j, (cacheT j).val ≠ 1) (hct : ∀ j, cacheT j ≠ terminal) (ht1 : terminal.val ≠ 1) :
    Function.Injective (gSS e hV da cacheT terminal hres hN) := by
  have hFB : d.F ≤ d.B := by
    unfold SourceConstruction.Dims.B SourceConstruction.Dims.G; omega
  have h1F : 1 < d.F := by have := e.ext2.ext1.ext.hF; omega
  -- a low port's value is below F; a high port's is at least B
  have lowv : ∀ z : Fin (NF + (19 + 4 * tS)), Low z.val → (gSS e hV da cacheT terminal hres hN z).val < d.F := by
    intro z hz
    unfold gSS
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
      unfold gSS at hab
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
      rw [hv', gSS_high e hV da cacheT terminal hres hN b lb] at h1
      omega
  · by_cases lb : Low b.val
    · have h1 := lowv b lb
      rw [← hv', gSS_high e hV da cacheT terminal hres hN a la] at h1
      omega
    · rw [gSS_high e hV da cacheT terminal hres hN a la, gSS_high e hV da cacheT terminal hres hN b lb] at hv'
      have hh : hv (restPc eX pX gW) (eX + pX) a.val = hv (restPc eX pX gW) (eX + pX) b.val := by omega
      have ia := hvinv_hv (eX + pX) gW a.val la (by have := a.isLt; omega)
      have ib := hvinv_hv (eX + pX) gW b.val lb (by have := b.isLt; omega)
      have e1 : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
      rw [e1] at hh
      rw [hh] at ia
      exact Fin.ext (ia.symm.trans ib)

end dockSym

/-- The ten FactorSelection residents' words for SYM (header fields in mode `true`). -/
def resWS (q Pw W Ld L target cwid cw i : Nat) : List Bool :=
  if i = 0 then UnaryTemplate.tape q else if i = 1 then List.replicate Pw true
  else if i = 2 then List.replicate W true else if i = 3 then List.replicate Ld true
  else if h : i < 8 then RepairOrdinary.frame (SourceFactorSel.Header.fields true q L target 0 ⟨i - 4, by omega⟩)
  else if i = 8 then List.replicate cwid true else List.replicate cw true

section SS
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
  (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tS) ≤ gW)

theorem gSS_out (z : Fin (NF + (19 + 4 * tS))) (h33 : 33 ≤ z.val) (h39 : z.val ≠ 39) :
    Rest.OutV d eX pX gW (gSS e hV da cacheT terminal hres hN z).val := by
  have hl : ¬ Low z.val := by unfold Low; omega
  rw [gSS_high e hV da cacheT terminal hres hN z hl]
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

end SS

section SelRunSS
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
  (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tS) ≤ gW)

theorem gSS_nT : gSS e hV da cacheT terminal hres hN (up 33) = Dims.pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩ :=
  Fin.ext (by
    rw [gSS_high e hV da cacheT terminal hres hN _ (by unfold Low; show ¬ (33 < 19 ∨ 33 = 19 ∨ 33 = 32); decide), up_val]
    show d.B + hv _ _ 33 = d.B + 19 + 70
    rw [hv_33])

theorem gSS_coefT (i : Fin 3) :
    gSS e hV da cacheT terminal hres hN (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) =
      Dims.pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩ :=
  Fin.ext (by
    have hi := i.isLt
    rw [gSS_high e hV da cacheT terminal hres hN _ (by unfold Low; show ¬ (34 + i.val < 19 ∨ 34 + i.val = 19 ∨ 34 + i.val = 32); omega),
      up_val]
    show d.B + hv _ _ (34 + i.val) = d.B + 19 + (61 + i.val)
    rw [hv_34 _ _ _ hi]; omega)

theorem gSS_regR (Pw W Ld gG7 : Nat) (hG : NF + (19 + 4 * tS) ≤ gG7) {n0 : Nat} {circuit : BooleanCircuit n0}
    (pcpp : PointwisePCPP circuit) (x : Fin (19 + 4 * (SelBackSym.PS (pcpp := pcpp) da Pw W Ld).t)) :
    d.B + 90 + eX + pX ≤ (gSS e hV da cacheT terminal hres hN (rgP (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) x)).val ∧
      (gSS e hV da cacheT terminal hres hN (rgP (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) x)).val < d.B + 90 + eX + pX + gG7 := by
  have hx : x.val < 19 + 4 * tS := x.isLt
  have hz : ¬ Low (NF + x.val) := by unfold Low NF; omega
  have e1 := gSS_high e hV da cacheT terminal hres hN (rgP (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) x) hz
  rw [e1, rg_val, hv_reg _ _ _ (by unfold NF; omega) (by unfold NF; omega)]
  exact ⟨by omega, by unfold NF at *; omega⟩

theorem gSS_scr (gG7 : Nat) (hG : NF + (19 + 4 * tS) ≤ gG7) (x : Fin V)
    (hx : ∃ z : Fin NF, 100 ≤ z.val ∧ gSS e hV da cacheT terminal hres hN (up z) = x) :
    d.B + 90 + eX + pX ≤ x.val ∧ x.val < d.B + 90 + eX + pX + gG7 := by
  obtain ⟨z, hz1, rfl⟩ := hx
  have hzl : z.val < NF := z.isLt
  have hz : ¬ Low z.val := by unfold Low; omega
  have e1 := gSS_high e hV da cacheT terminal hres hN (up z) hz
  rw [up_val] at e1
  rw [e1, hv_reg _ _ _ (by omega) (by omega)]
  exact ⟨by omega, by unfold NF at *; omega⟩

end SelRunSS

end
end NearCubicWires.SourceRequest.SelLocal

