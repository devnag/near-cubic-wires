import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.VectorCounter

/-! The resident half-window W physically supplies the 2W+1 outer driver:
two actual W-counted increment loops and one final increment. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowWidthDriver
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def A (R n W : Nat) : Fin 2→List Bool :=
  ![ZeroPadding.pad R (CompareMachine.word n),ZeroPadding.pad R (CompareMachine.word W)]
def count := RepeatMachine.machine VectorCounter.increment (fun _ _=>true)
def increment := TapeEmbedding.machine 1 VectorCounter.increment
def up := Completion.PhysicalDriverMoves.machine 2 .right
def down := Completion.PhysicalDriverMoves.machine 2 .left
def machine := Composition.machine up (Composition.machine count
  (Composition.machine count (Composition.machine increment down)))
def loopBudget (W : Nat) := W*(4*W+5)+3
def budget (W : Nat) := 2*loopBudget W+4*W+8

theorem count_run (R n W : Nat) (hn : n≤W) :
    Step count (loopBudget W) (fun _=>1) (A R n W) (fun _=>1) (A R (n+W) W) := by
  have h:=PhysicalRepeatStep.run VectorCounter.increment W (4*W+2)
    (fun _ _=>1) (fun j _=>ZeroPadding.pad R (CompareMachine.word (n+j)))
    (fun j hj=>by
      have one:=VectorCounter.increment_padded (n+j) R
      have bound : 2*(n+j)+2≤4*W+2 := by omega
      simpa only [Nat.add_assoc] using one.enlarge bound)
  have padded:=h.pad (![0,R] : Fin 2→Nat)
  convert padded using 1 <;>first | rfl |
    (funext i;fin_cases i <;>simp [A,Fin.addCases,ZeroPadding.pad_zero])

theorem increment_run (R W : Nat) :
    Step increment (4*W+2) (fun _=>1) (A R (2*W) W) (fun _=>1) (A R (2*W+1) W) := by
  have h:=(VectorCounter.increment_padded (2*W) R).embed
    (fun _ : Fin 1=>1) (fun _=>ZeroPadding.pad R (CompareMachine.word W))
  convert h using 1 <;>first | rfl | omega | (funext i;fin_cases i <;>rfl)

theorem run (R W : Nat) :
    Step machine (budget W) (fun _=>0) (A R 0 W) (fun _=>0) (A R (2*W+1) W) := by
  have upRun:=Completion.PhysicalDriverMoves.run .right (fun _ : Fin 2=>0) (A R 0 W)
  have downRun:=Completion.PhysicalDriverMoves.run .left (fun _ : Fin 2=>1) (A R (2*W+1) W)
  have first:=count_run R 0 W (by omega)
  have second:=count_run R W W le_rfl
  simp only [Nat.zero_add] at first
  rw [show W+W=2*W by omega] at second
  have all:=upRun.seq (first.seq (second.seq ((increment_run R W).seq downRun)))
  have fuel : 1+1+(loopBudget W+1+(loopBudget W+1+((4*W+2)+1+1)))=budget W := by
    unfold budget;omega
  simpa only [machine,up,down,fuel,HeadMove.apply] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowWidthDriver
