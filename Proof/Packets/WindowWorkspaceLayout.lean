import Proof.Packets.WindowWorkspace
import Proof.Packets.WindowNativeDock
import Proof.Packets.SubstitutionPrepareCopies

/-! Exact ready-bank identities after the actual provider workspace sweep.
The existing arithmetic masters supply both normalizer templates and logs. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider.Workspace
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

theorem core_retained (R : Nat) (A : Fin 256→List Bool) (i : Fin 34) :
    cleared R A (i.castAdd 222)=A (i.castAdd 222) := by
  have hn : ¬selected (i.castAdd 222) := by
    simp only [selected,Fin.val_castAdd]
    have h:=i.isLt
    omega
  rw [cleared,if_neg hn]

theorem native_ready (C R : Nat) (left right : List (List Bool)) (A : Fin 256→List Bool)
    (ha : ∀ i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀ i,cleared R A (nativePorts i)=ReusableNative.ready C R right i := by
  have e13 : A 13=ZeroPadding.pad R (UnaryTemplate.tape (2*C+3)):=ha 13
  have e24 : A 24=ZeroPadding.pad R (UnaryTemplate.tape C):=ha 24
  have e26 : A 26=ZeroPadding.pad R right.flatten:=ha 26
  have e27 : A 27=ZeroPadding.pad R (CompareMachine.word right.length):=ha 27
  have e30 : A 30=List.replicate (R+3) false:=ha 30
  have e31 : A 31=UnaryTemplate.tape R:=ha 31
  have e32 : A 32=List.replicate R true:=ha 32
  have e33 : A 33=List.replicate (R+3) false:=ha 33
  intro i
  fin_cases i <;>simp [cleared,selected,nativePorts,ReusableNative.ready,
    ReusableNative.bank,ReusableNative.readyData,Fin.addCases,e13,e24,e26,e27,e30,e31,e32,e33]

theorem substitution_ready (C R : Nat) (left right : List (List Bool)) (A : Fin 256→List Bool)
    (ha : ∀ i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀ i,cleared R A (substitutionPorts i)=SubstitutionCall.resident C R left right (A 140) i := by
  intro i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · rw [substitutionPorts,Fin.addCases_left,core_retained,ha]
    unfold SubstitutionCall.resident
    rw [Fin.addCases_left]
  · fin_cases j <;>simp [substitutionPorts,cleared,selected,SubstitutionCall.resident,Fin.addCases]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider.Workspace
