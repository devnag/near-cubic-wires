import Proof.Packets.SubstitutionPrepareCopies
import Proof.Packets.SubstitutionScratchErase

/-! Cold physical allocation of the nine private substitution tapes. The
arithmetic arena and atom bank are retained verbatim. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def coldResident (C R : Nat) (left right : Packet) (atoms : List Bool) : Fin 44→List Bool :=
  Fin.addCases (m:=34) (n:=10) (ReusableArithmetic.state C R left right) (fun i=>if i=0 then atoms else [])

theorem allocate_run (C R : Nat) (left right : Packet) (atoms : List Bool) :
    Step SubstitutionScratch.machine (2*R+4) heads (coldResident C R left right atoms)
      heads (resident C R left right atoms) := by
  have hf : ∀ i : Fin 44,35 ≤ i.val→(coldResident C R left right atoms i).length≤R := by
    intro i
    refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
    · intro hi;have hj:=j.isLt;simp only [Fin.val_castAdd] at hi;omega
    · intro hi
      have hj : j≠0 := by intro he;subst j;simp at hi
      unfold coldResident
      rw [Fin.addCases_right,if_neg hj]
      simp
  have h:=SubstitutionScratch.run R heads (coldResident C R left right atoms)
    (by intro j;fin_cases j <;>rfl) rfl rfl hf
  apply h.congr rfl
  funext i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · have hn : ¬35 ≤ (j.castAdd 10).val := by simp only [Fin.val_castAdd];omega
    rw [SubstitutionScratch.cleared,if_neg hn]
    unfold coldResident resident
    rw [Fin.addCases_left,Fin.addCases_left]
  · unfold resident
    rw [Fin.addCases_right]
    by_cases hj : j=0
    · subst j;rfl
    · have hn : 35 ≤ (j.natAdd 34).val := by
        have hz : j.val≠0 := by intro he;apply hj;exact Fin.ext he
        simp only [Fin.val_natAdd];omega
      simp only [SubstitutionScratch.cleared,if_pos hn,if_neg hj]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
