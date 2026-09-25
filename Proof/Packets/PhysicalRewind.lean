import Proof.Rows.PhysicalFocusBoundary

/-! Execute a program and pay for its rewind from an empty log tape. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace Completion.PhysicalColdRewind
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem run {t s n : Nat} {p : Machine t s} {input output : Fin t→List Bool}
    {heads : Fin t→Nat} (h : Step p n (fun _=>0) input heads output) :
    ∃ k≤n, Step (Rewind.machine p) (2*n+2) (fun _=>0)
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) input (fun _=>[]))
      (fun _=>0)
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) output
        (fun _=>List.replicate k false)) := by
  obtain ⟨source,hs,_,ht,hsteps⟩:=h
  change LocalBitMultitape.run p n input=some source at hs
  obtain ⟨r,hr,rt,rl,rh,rs,_⟩:=Rewind.Workspace.reset_workspace p n input source hs 0
  have bound : 2*source.steps+2≤2*n+2 := by omega
  have more:=runFrom_moreFuel (Rewind.machine p) (2*source.steps+2)
    (2*n+2-(2*source.steps+2)) _ r hr
  rw [Nat.add_sub_of_le bound] at more
  refine ⟨source.steps,hsteps,r,more,funext rh,?_,by omega⟩
  funext i
  refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simpa only [Fin.addCases_left,ht] using rt j
  · have hj : j=0:=Fin.eq_zero j
    subst hj
    simpa only [Fin.addCases_right,Nat.zero_max] using rl

end
end Completion.PhysicalColdRewind
