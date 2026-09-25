import Proof.Packets.PacketsXVectorNumericArena
import Proof.Packets.PhysicalCounterCopyZero

/-! Child/parent Repeat drivers are physically copied from the population
master and incremented. The descending depth driver is copied from the actual
level counter. All three retained masters survive the boot. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def childDriver := PhysicalCounterCopy.zeroSuccessor (31 : Fin 299) 281 296
def parentDriver := PhysicalCounterCopy.zeroSuccessor (31 : Fin 299) 281 297
def depthDriver := PhysicalCounterCopy.machine (31 : Fin 299) 260 298
def bootDrivers := Composition.machine (Composition.machine childDriver parentDriver) depthDriver
def driverData (R M depth : Nat) (A : Fin 299→List Bool) :=
  Function.update (Function.update (Function.update A 296 (ZeroPadding.pad R (CompareMachine.word (M+1))))
    297 (ZeroPadding.pad R (CompareMachine.word (M+1)))) 298 (ZeroPadding.pad R (CompareMachine.word depth))

theorem drivers_run (R M depth : Nat) (A : Fin 299→List Bool)
    (hR : A 31=UnaryTemplate.tape R)
    (hM : A 281=ZeroPadding.pad R (CompareMachine.word M))
    (hD : A 260=ZeroPadding.pad R (CompareMachine.word depth))
    (hm : M+2≤R) (hd : depth+1≤R)
    (h296 : (A 296).length=R) (h297 : (A 297).length=R) (h298 : (A 298).length=R) :
    Step bootDrivers (6*R+4*M+30) heads A heads (driverData R M depth A) := by
  have first:=PhysicalCounterCopy.zero_successor_run R M (31 : Fin 299) 281 296
    (by decide) (by decide) (by decide) heads A rfl rfl rfl hR hM (by omega) h296
  have second:=PhysicalCounterCopy.zero_successor_run R M (31 : Fin 299) 281 297
    (by decide) (by decide) (by decide) heads
    (Function.update A 296 (ZeroPadding.pad R (CompareMachine.word (M+1))))
    rfl rfl rfl (by simpa [Function.update] using hR)
    (by simpa [Function.update] using hM) (by omega) (by simpa [Function.update] using h297)
  have last:=PhysicalCounterCopy.run R (31 : Fin 299) 260 298
    (by decide) (by decide) (by decide) heads
    (Function.update (Function.update A 296 (ZeroPadding.pad R (CompareMachine.word (M+1))))
      297 (ZeroPadding.pad R (CompareMachine.word (M+1))))
    rfl rfl rfl (by simpa [Function.update] using hR)
    (by simp [Function.update,hD,ZeroPadding.pad_length,CompareMachine.word];omega)
    (by simpa [Function.update] using h298)
  have whole:=(first.seq second).seq last
  have budget : ((2*R+2*M+9)+1+(2*R+2*M+9))+1+(2*R+10)=6*R+4*M+30 := by omega
  rw [budget] at whole
  simpa only [bootDrivers,childDriver,parentDriver,depthDriver,driverData,Function.update_of_ne (by decide : (260 : Fin 299)≠297),
    Function.update_of_ne (by decide : (260 : Fin 299)≠296),hD] using whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
