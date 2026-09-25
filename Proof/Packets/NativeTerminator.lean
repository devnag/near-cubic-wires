import Proof.MachineModel.Runs

/-! One paid native stream terminator; the append cursor is explicit. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeTerminator
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

def machine : Machine 1 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>some false,fun _=>.right⟩ else none

theorem run (out : List Bool) : Step machine 1 (fun _=>out.length) (fun _=>out)
    (fun _=>(out++[false]).length) (fun _=>out++[false]) := by
  have hs : step machine (⟨0,fun _=>out.length,fun _=>out⟩ : Configuration 1 2)=
      some ⟨1,fun _=>(out++[false]).length,fun _=>out++[false]⟩ := by
    simp [step,machine]
    apply configuration_ext
    · rfl
    · funext i;simp [applyAction,HeadMove.apply]
    · funext i;exact Streaming.write_append out false
  obtain ⟨r,rr,rf,_⟩:=(Timed.single (by rfl : machine.halted (0 : Fin 2)=false) hs).run (by rfl)
  exact Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeTerminator
