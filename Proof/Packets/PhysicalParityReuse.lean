import Proof.Packets.PhysicalParity

namespace NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityReuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev rawSize := 2+((ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size))+2)
abbrev size := rawSize+2
noncomputable def finalCode : Fin size := (1 : Fin 2).natAdd rawSize
def cfg {s : ℕ} (q : Fin s) (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap : ℕ) : Configuration 5 s :=
  ⟨q,![lp,rp,0,0,0],![left,right,[eq],[found],List.replicate cap false]⟩

theorem input_eq (q : Fin rawSize) (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap : ℕ) :
    ZeroPadding.config (Rewind.Workspace.capacities 4 cap)
      (Rewind.recording (PhysicalParityProbe.cfg q left right lp rp eq found) 0)=
      cfg (q.castAdd 2) left right lp rp eq found cap := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,Rewind.recording,Rewind.config,PhysicalParityProbe.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,PhysicalParityProbe.cfg,cfg,Fin.addCases,ZeroPadding.pad]

theorem output_eq (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap : ℕ) :
    SelectiveReset.finished (s := rawSize) ![lp,rp,0,0] ![left,right,[eq],[found]] cap=
      cfg finalCode left right lp rp eq found cap := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,Fin.addCases]
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,Fin.addCases]

end NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityReuse
