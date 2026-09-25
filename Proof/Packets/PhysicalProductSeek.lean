import Proof.Packets.PhysicalRepeatStep
import Proof.Rows.PhysicalDriverMoves

/-! Paid forward movement by a product of two resident unary counts. No
computed product word or destination head position is supplied to the machine. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalProductSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def inner := RepeatMachine.machine (Completion.PhysicalDriverMoves.machine 1 .right) (fun _ _=>true)
noncomputable def machine := RepeatMachine.machine inner (fun _ _=>true)
def budget (C M : Nat) := M*(4*C+6)+3

theorem inner_run (C position : Nat) (source : List Bool) :
    Step inner (4*C+3) (![position,1]) (![source,CompareMachine.word C])
      (![position+C,1]) (![source,CompareMachine.word C]) := by
  have h:=PhysicalRepeatStep.run (Completion.PhysicalDriverMoves.machine 1 .right) C 1
    (fun k _=>position+k) (fun _ _=>source) (by
      intro k _
      simpa only [HeadMove.apply,Nat.add_assoc] using
        Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>position+k) (fun _=>source))
  have hs : C*(1+3)+3=4*C+3 := by omega
  rw [hs] at h
  simp only [Nat.add_zero] at h
  convert h using 1 <;> first | rfl | (funext i;fin_cases i <;>rfl)

theorem run (C M position : Nat) (source : List Bool) :
    Step machine (budget C M)
      (![position,1,1]) (![source,CompareMachine.word C,CompareMachine.word M])
      (![position+M*C,1,1]) (![source,CompareMachine.word C,CompareMachine.word M]) := by
  have h:=PhysicalRepeatStep.run inner M (4*C+3)
    (fun k=>(![position+k*C,1] : Fin 2→Nat))
    (fun _=>(![source,CompareMachine.word C] : Fin 2→List Bool)) (by
      intro k _
      have hk : position+(k+1)*C=position+k*C+C := by ring
      simpa only [hk] using inner_run C (position+k*C) source)
  have hs : M*((4*C+3)+3)+3=budget C M := by unfold budget;ring
  rw [hs] at h
  simp only [Nat.zero_mul,Nat.add_zero] at h
  convert h using 1 <;> first | rfl | (funext i;fin_cases i <;>rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalProductSeek
