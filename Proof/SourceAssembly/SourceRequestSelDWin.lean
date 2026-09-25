import Proof.SourceAssembly.SourceSkelInitK

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelDWin
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

theorem dwin_site (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (q : Nat) (mode : Bool) :
    q + 2 ≤ SourceSkeleton.Params.dC sources gamma hg hh p * (q+1) ^ SourceSkeleton.Params.dE sources gamma hg hh p ∧
    SourceSkeleton.Params.pC sources gamma hg hh p * (q+1) ^ SourceSkeleton.Params.pE sources gamma hg hh p ≤
      SourceSkeleton.Params.dC sources gamma hg hh p * (q+1) ^ SourceSkeleton.Params.dE sources gamma hg hh p ∧
    SourceBudget.wCap q ≤ SourceSkeleton.Params.dC sources gamma hg hh p * (q+1) ^ SourceSkeleton.Params.dE sources gamma hg hh p ∧
    SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p) q ≤
      SourceSkeleton.Params.dC sources gamma hg hh p * (q+1) ^ SourceSkeleton.Params.dE sources gamma hg hh p ∧
    2 * SourceSkeleton.InitS.cwidOf mode
        (SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p) q) + 1 ≤
      SourceSkeleton.Params.dC sources gamma hg hh p * (q+1) ^ SourceSkeleton.Params.dE sources gamma hg hh p := by
  have h := SourceSkeleton.Params.dSum_le_D sources gamma hg hh p q
  unfold SourceSkeleton.Params.dSum at h
  have hc : SourceSkeleton.InitS.cwidOf mode
      (SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p) (SourceSkeleton.Params.ldE sources gamma hg hh p) q) ≤
      SourceRequest.ThrSwitch.codeWidth (SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p)
        (SourceSkeleton.Params.ldE sources gamma hg hh p) q) +
      SourceRequest.SymOriginal.symCodeWidth (SourceBudget.ldCap (SourceSkeleton.Params.ldC sources gamma hg hh p)
        (SourceSkeleton.Params.ldE sources gamma hg hh p) q) := by
    unfold SourceSkeleton.InitS.cwidOf
    cases mode
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

end
end NearCubicWires.SourceRequest.SelDWin

