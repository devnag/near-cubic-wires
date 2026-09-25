import Proof.Packets.PhysicalIndexReload

/-! Three actual fixed-width copies overwrite reusable targets and restore
every head. The source words and width template are retained literally. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalTripleCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def data (R : Nat) (source target : Fin 3 → List Bool) : Fin 7 → List Bool :=
  ![UnaryTemplate.tape R,source 0,source 1,source 2,target 0,target 1,target 2]
def H (i : Fin 7) : Nat := if i=0 then 1 else 0
def machine := Composition.machine (PhysicalIndexReload.move (0 : Fin 7) .right)
  (Composition.machine (PhysicalCopyInto.machine (0 : Fin 7) 1 4)
    (Composition.machine (PhysicalCopyInto.machine (0 : Fin 7) 2 5)
      (Composition.machine (PhysicalCopyInto.machine (0 : Fin 7) 3 6)
        (PhysicalIndexReload.move (0 : Fin 7) .left))))

theorem run (R : Nat) (source target : Fin 3 → List Bool)
    (hs : ∀i,(source i).length=R) (ht : ∀i,(target i).length=R) :
    Step machine (6*R+12) (fun _=>0) (data R source target)
      (fun _=>0) (data R source source) := by
  let A0:=data R source target
  let A1:=Function.update A0 4 (source 0)
  let A2:=Function.update A1 5 (source 1)
  let A3:=Function.update A2 6 (source 2)
  have raised : Function.update (fun _ : Fin 7=>0) 0 (HeadMove.right.apply 0)=H := by
    funext i;simp [H,Function.update,HeadMove.apply]
  have up:=(PhysicalIndexReload.move_run (0 : Fin 7) .right (fun _=>0) A0).congr raised rfl
  have first : Step (PhysicalCopyInto.machine (0 : Fin 7) 1 4) (2*R+2) H A0 H A1 := by
    apply PhysicalCopyInto.run R 0 1 4 (by decide) (by decide) (by decide)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hs 0
    · exact ht 0
  have second : Step (PhysicalCopyInto.machine (0 : Fin 7) 2 5) (2*R+2) H A1 H A2 := by
    apply PhysicalCopyInto.run R 0 2 5 (by decide) (by decide) (by decide)
    · rfl
    · rfl
    · rfl
    · simp [A1,A0,data,Function.update]
    · simpa [A1,A0,data,Function.update] using hs 1
    · simpa [A1,A0,data,Function.update] using ht 1
  have third : Step (PhysicalCopyInto.machine (0 : Fin 7) 3 6) (2*R+2) H A2 H A3 := by
    apply PhysicalCopyInto.run R 0 3 6 (by decide) (by decide) (by decide)
    · rfl
    · rfl
    · rfl
    · simp [A2,A1,A0,data,Function.update]
    · simpa [A2,A1,A0,data,Function.update] using hs 2
    · simpa [A2,A1,A0,data,Function.update] using ht 2
  have lowered : Function.update H 0 (HeadMove.left.apply (H 0))=(fun _=>0) := by
    funext i;simp [H,Function.update,HeadMove.apply]
  have finish : A3=data R source source := by
    funext i;fin_cases i <;>simp [A3,A2,A1,A0,data,Function.update]
  have down:=(PhysicalIndexReload.move_run (0 : Fin 7) .left H A3).congr lowered finish
  have all:=up.seq (first.seq (second.seq (third.seq down)))
  simpa only [machine,show 1+1+((2*R+2)+1+((2*R+2)+1+((2*R+2)+1+1)))=6*R+12 by omega] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalTripleCopy
