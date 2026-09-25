import Proof.Packets.PacketsXVectorWorkerArena
import Proof.Packets.PhysicalCounterCopy

/-! Runtime literal tag from the actual descending level counter. Terminal
tag zero and delta tag level+1 are both physically written into provider187. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def deltaTag := Composition.machine (PhysicalIndexReload.move (187 : Fin 296) .right)
  (Composition.machine (PhysicalCounterCopy.successor (31 : Fin 296) 260 187)
    (PhysicalIndexReload.move (187 : Fin 296) .left))

theorem delta_tag_run (R level : Nat) (A : Fin 296→List Bool)
    (hw : A 31=UnaryTemplate.tape R)
    (hl : A 260=ZeroPadding.pad R (CompareMachine.word level))
    (hlevel : level+1≤R) (ht : (A 187).length=R) :
    Step deltaTag (2*R+2*level+17) heads A heads
      (Function.update A 187 (ZeroPadding.pad R (CompareMachine.word (level+1)))) := by
  have first:=PhysicalIndexReload.move_run (187 : Fin 296) .right heads A
  change Step _ 1 heads A (Function.update heads 187 1) A at first
  have middle:=PhysicalCounterCopy.successor_run R level (31 : Fin 296) 260 187
    (by decide) (by decide) (by decide) (Function.update heads 187 1) A
    (by decide) (by decide) (by simp) hw hl hlevel ht
  have last:=PhysicalIndexReload.move_run (187 : Fin 296) .left (Function.update heads 187 1)
    (Function.update A 187 (ZeroPadding.pad R (CompareMachine.word (level+1))))
  simp only [Function.update_self,HeadMove.apply] at last
  have he : Function.update (Function.update heads 187 1) 187 0=heads := by
    funext i;by_cases hi:i=187
    · subst i;rfl
    · simp only [Function.update_of_ne hi]
  have whole:=first.seq (middle.seq (last.congr he rfl))
  have hf : 1+1+((2*R+2*level+13)+1+1)=2*R+2*level+17 := by omega
  rw [hf] at whole;exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
