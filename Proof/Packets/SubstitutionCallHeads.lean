import Proof.Packets.SubstitutionCallLayout
import Proof.Packets.PhysicalProductSeek

/-! Paid cursor setup and restoration for the reusable substitution call. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def movedHeads (d : HeadMove) (H : Fin 44→Nat) :=
  Function.update (Function.update (Function.update H 35 (d.apply (H 35))) 38 (d.apply (H 38))) 43 (d.apply (H 43))
noncomputable def moveDrivers (d : HeadMove) := Composition.machine (PhysicalIndexReload.move (35 : Fin 44) d)
  (Composition.machine (PhysicalIndexReload.move (38 : Fin 44) d) (PhysicalIndexReload.move (43 : Fin 44) d))

theorem move_drivers_run (d : HeadMove) (H : Fin 44→Nat) (A : Fin 44→List Bool) :
    Step (moveDrivers d) 5 H A (movedHeads d H) A := by
  exact (PhysicalIndexReload.move_run 35 d H A).seq
    ((PhysicalIndexReload.move_run 38 d (Function.update H 35 (d.apply (H 35))) A).seq
      (PhysicalIndexReload.move_run 43 d (Function.update (Function.update H 35 (d.apply (H 35)))
        38 (d.apply (H 38))) A))

theorem loop_heads_core (position : Nat) (i : Fin 34) :
    loopHeads position (i.castAdd 10)=ReusableArithmetic.heads i := by
  have e : i.castAdd 10=(i.castAdd 9).castAdd 1 := rfl
  rw [e]
  unfold loopHeads
  rw [Fin.addCases_left,SubstitutionOuter.H_core]

theorem loop_heads_extra (position : Nat) (i : Fin 10) :
    loopHeads position (i.natAdd 34)=(![0,1,0,position,1,0,0,0,0,1] : Fin 10→Nat) i := by
  refine Fin.addCases (m:=9) (n:=1) (fun j=>?_) (fun j=>?_) i
  · have e : (j.castAdd 1).natAdd 34=(j.natAdd 34).castAdd 1 := rfl
    rw [e]
    unfold loopHeads
    rw [Fin.addCases_left,SubstitutionOuter.H_extra]
    fin_cases j <;>rfl
  · fin_cases j;rfl

theorem moved_up : movedHeads .right heads=loopHeads 0 := by
  funext i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · rw [loop_heads_core]
    have hn (n : Fin 44) (h : 34≤n.val) : j.castAdd 10≠n := by
      intro he;have hv:=congrArg Fin.val he;have hj:=j.isLt;simp only [Fin.val_castAdd] at hv;omega
    simp only [movedHeads,Function.update_of_ne (hn 43 (by decide)),
      Function.update_of_ne (hn 38 (by decide)),Function.update_of_ne (hn 35 (by decide)),heads,Fin.addCases_left]
  · rw [loop_heads_extra]
    fin_cases j <;>rfl

theorem moved_down : movedHeads .left (loopHeads 0)=heads := by
  funext i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · have hn (n : Fin 44) (h : 34≤n.val) : j.castAdd 10≠n := by
      intro he;have hv:=congrArg Fin.val he;have hj:=j.isLt;simp only [Fin.val_castAdd] at hv;omega
    simp only [movedHeads,Function.update_of_ne (hn 43 (by decide)),
      Function.update_of_ne (hn 38 (by decide)),Function.update_of_ne (hn 35 (by decide)),
      loop_heads_core,heads,Fin.addCases_left]
  · fin_cases j <;>rfl

def seekPorts : Fin 3→Fin 44 := ![37,38,43]
noncomputable def seek := RecoveryFocus.machine seekPorts PhysicalProductSeek.machine

theorem seek_run (C R M position : Nat) (left stored : Packet) (atoms source : List Bool) :
    Step seek (PhysicalProductSeek.budget C M) (loopHeads position)
      (loopTapes C R M left stored atoms source) (loopHeads (position+M*C))
      (loopTapes C R M left stored atoms source) := by
  have h:=(PhysicalProductSeek.run C M position source).pad (fun _=>R)
  apply PhysicalFocusBoundary.focus h seekPorts (by decide) (loopHeads position) (loopHeads (position+M*C)) _ _
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>rfl
  · intro i away
    refine ⟨?_,rfl⟩
    have hn : i≠37 := by intro he;subst i;exact away 0 rfl
    revert hn
    refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
    · intro _;rw [loop_heads_core,loop_heads_core]
    · intro hn;rw [loop_heads_extra,loop_heads_extra]
      fin_cases j <;> first |rfl | exact False.elim (hn rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
