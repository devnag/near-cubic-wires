import Proof.Packets.PacketsXVectorWorkerArena
import Proof.Packets.PhysicalBitCall

/-! Both delta validity flags are read physically. A paid zeroing of the right
packet precedes the conditional provider; invalid targets therefore produce
exactly the zero polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 296) 0 26)
  (PhysicalCopyInto.machine (31 : Fin 296) 0 27)
def rightZero (R : Nat) (A : Fin 296→List Bool) :=
  Function.update (Function.update A 26 (List.replicate R false)) 27 (List.replicate R false)
def guarded {s : Nat} (provider : Machine 296 s) :=
  PhysicalBitCall.machine (276 : Fin 296) (PhysicalBitCall.machine (279 : Fin 296) provider)
def deltaBranch {s : Nat} (provider : Machine 296 s) := Composition.machine zeroRight (guarded provider)

theorem zero_right_run (R : Nat) (A : Fin 296→List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hp : (A 26).length=R) (hc : (A 27).length=R) :
    Step zeroRight (4*R+5) heads A heads (rightZero R A) := by
  have first:=PhysicalCopyInto.run R (31 : Fin 296) 0 26 (by decide) (by decide) (by decide)
    heads A rfl rfl rfl hw (by rw [hz,List.length_replicate]) hp
  have last:=PhysicalCopyInto.run R (31 : Fin 296) 0 27 (by decide) (by decide) (by decide)
    heads (Function.update A 26 (A 0)) rfl rfl rfl
    (by simpa [Function.update] using hw) (by simp [Function.update,hz])
    (by simpa [Function.update] using hc)
  have whole:=first.seq last
  have hf : (2*R+2)+1+(2*R+2)=4*R+5 := by omega
  rw [hf] at whole
  simpa [zeroRight,rightZero,Function.update_of_ne (by decide : (0 : Fin 296)≠26),hz] using whole

theorem guarded_true {s fuel : Nat} {p : Machine 296 s} {A B : Fin 296→List Bool}
    (hlo : readTapeBit (A 276) 0=true) (hhi : readTapeBit (A 279) 0=true)
    (hp : Step p fuel heads A heads B) :
    Step (guarded p) (fuel+6) heads A heads B := by
  exact PhysicalBitCall.run_true 276 hlo (PhysicalBitCall.run_true 279 hhi hp)

theorem guarded_false {s : Nat} (p : Machine 296 s) (A : Fin 296→List Bool)
    (hbad : readTapeBit (A 276) 0=false ∨ readTapeBit (A 279) 0=false) :
    Step (guarded p) 5 heads A heads A := by
  rcases hbad with hlo|hhi
  · exact (PhysicalBitCall.run_false (p:=PhysicalBitCall.machine (279 : Fin 296) p) 276 heads A hlo).enlarge (by omega)
  · cases hlo : readTapeBit (A 276) 0
    · exact (PhysicalBitCall.run_false (p:=PhysicalBitCall.machine (279 : Fin 296) p) 276 heads A hlo).enlarge (by omega)
    · exact PhysicalBitCall.run_true 276 hlo (PhysicalBitCall.run_false (p:=p) 279 heads A hhi)

theorem branch_valid {s fuel : Nat} {p : Machine 296 s} (R : Nat) (A B : Fin 296→List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hp : (A 26).length=R) (hc : (A 27).length=R)
    (hlo : readTapeBit (A 276) 0=true) (hhi : readTapeBit (A 279) 0=true)
    (provider : Step p fuel heads (rightZero R A) heads B) :
    Step (deltaBranch p) (4*R+fuel+12) heads A heads B := by
  have last:=guarded_true (by simpa [rightZero,Function.update] using hlo)
    (by simpa [rightZero,Function.update] using hhi) provider
  have whole:=(zero_right_run R A hw hz hp hc).seq last
  have hf : (4*R+5)+1+(fuel+6)=4*R+fuel+12 := by omega
  rw [hf] at whole;exact whole

theorem branch_invalid {s : Nat} (p : Machine 296 s) (R : Nat) (A : Fin 296→List Bool)
    (hw : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hp : (A 26).length=R) (hc : (A 27).length=R)
    (hbad : readTapeBit (A 276) 0=false ∨ readTapeBit (A 279) 0=false) :
    Step (deltaBranch p) (4*R+11) heads A heads (rightZero R A) := by
  have last:=guarded_false p (rightZero R A) (by simpa [rightZero,Function.update] using hbad)
  have whole:=(zero_right_run R A hw hz hp hc).seq last
  have hf : (4*R+5)+1+5=4*R+11 := by omega
  rw [hf] at whole;exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
