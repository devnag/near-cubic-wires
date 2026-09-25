import Proof.SourceAssembly.SourceSkelInitK

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceFactorSel.H5
open NearCubicWires.SourceSkeleton.Params

theorem ports_le_D (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) (q : ℕ) :
    q + 2 ≤ dC sources gamma hg hh p * (q+1)^dE sources gamma hg hh p ∧
    pC sources gamma hg hh p * (q+1)^pE sources gamma hg hh p ≤ dC sources gamma hg hh p * (q+1)^dE sources gamma hg hh p ∧
    SourceBudget.wCap q ≤ dC sources gamma hg hh p * (q+1)^dE sources gamma hg hh p ∧
    SourceBudget.ldCap (ldC sources gamma hg hh p) (ldE sources gamma hg hh p) q ≤
      dC sources gamma hg hh p * (q+1)^dE sources gamma hg hh p := by
  have h := dSum_le_D sources gamma hg hh p q
  unfold dSum at h
  refine ⟨by omega, by omega, by omega, by omega⟩

end NearCubicWires.SourceFactorSel.H5
end

