import Proof.Packets.SrcMetaCost
import Proof.SourceAssembly.SourceFactorSelWordsWin

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceFactorSel.YbFit
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.Admission
open NearCubicWires.SourceFactorSel.WordsCost
noncomputable section

/-- **`Yb` at an admitted call**, for any meta word. -/
theorem Yb_le (a : DecompositionAlgorithm) {den degree target : ℕ} (hden : 1 ≤ den) (r : Request)
    (hr : RequestAdmitted den degree target r) (L : ℕ) (hL : r.liveScale = L) (MB : List Bool) :
    Yb a (r, MB) ≤ (inC0 a degree target + 4 * L) * (r.q + 1) ^ inE0 a degree target +
      2 * (betaC a degree * (r.q + 1) ^ betaE a degree) + MB.length + 1 := by
  have h1 := inFit a hden r hr L hL
  have h2 := gsFit a hden r hr
  have h3 := gs_le_exact (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs
  show (r.input a).length + (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length +
    (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs.length + MB.length + 1 ≤ _
  omega

theorem Yb_le_meta (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ)
    (a : DecompositionAlgorithm) {den degree target : ℕ} (hden : 1 ≤ den) (r : Request)
    (hr : RequestAdmitted den degree target r) (hL : r.liveScale = L) :
    Yb a (r, NearCubicWires.SourceStart.MetaRun.MBof selector s p packets L r.q) ≤
      (inC0 a degree target + 4 * L) * (r.q + 1) ^ inE0 a degree target +
      2 * (betaC a degree * (r.q + 1) ^ betaE a degree) +
      (40 * NearCubicWires.SourceStart.MetaCost.Sz selector s p packets L r.q + 200) + 1 := by
  have hY := Yb_le a hden r hr L hL (NearCubicWires.SourceStart.MetaRun.MBof selector s p packets L r.q)
  have hM := NearCubicWires.SourceStart.MetaCost.MB_len selector s p packets L
    (decide (NearCubicWires.SourceStart.Meta.mC selector s p r.q = 0))
    (decide (NearCubicWires.SourceStart.Meta.mV selector s p r.q = 0)) r.q
    (by simp only [decide_eq_true_iff]) (by simp only [decide_eq_true_iff])
  have hP := NearCubicWires.SourceStart.MetaCost.pieces_sum_le selector s p packets L
    (decide (NearCubicWires.SourceStart.Meta.mC selector s p r.q = 0))
    (decide (NearCubicWires.SourceStart.Meta.mV selector s p r.q = 0)) r.q
  omega

end
end NearCubicWires.SourceFactorSel.YbFit
end

