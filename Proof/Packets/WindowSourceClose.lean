import Proof.Packets.NativeTerminator
import Proof.Packets.PhysicalRewindInto

/-! Physically terminate the generated window stream and rewind it with the
actual reserve driver. Both operations are included in the provider budget. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def terminatorPorts : Fin 1→Fin 256 := fun _=>78
noncomputable def terminate := RecoveryFocus.machine terminatorPorts NativeTerminator.machine
noncomputable def closeSource := Composition.machine terminate (PhysicalRewindInto.machine (31 : Fin 256) 78)

theorem terminate_run (R : Nat) (body : List Bool) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hh : H 78=body.length) (ha : A 78=ZeroPadding.pad R body) :
    Step terminate 1 H A (Function.update H 78 (body.length+1))
      (Function.update A 78 (ZeroPadding.pad R (body++[false]))) := by
  have h:=(NativeTerminator.run body).pad (fun _=>R)
  apply PhysicalFocusBoundary.focus h terminatorPorts (by intro i j _;exact Subsingleton.elim i j)
    H (Function.update H 78 (body.length+1)) A (Function.update A 78 (ZeroPadding.pad R (body++[false])))
  · intro i;exact hh.symm
  · intro i;exact ha.symm
  · intro i;simp [terminatorPorts]
  · intro i;simp [terminatorPorts]
  · intro i away
    have hn : i≠78 := by intro he;subst i;exact away 0 rfl
    exact ⟨by simp [Function.update,hn],by simp [Function.update,hn]⟩

theorem close_source_run (R : Nat) (body : List Bool) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hh : H 78=body.length) (ha : A 78=ZeroPadding.pad R body)
    (hw : H 31=1) (hR : A 31=UnaryTemplate.tape R) (hfit : body.length+1≤R) :
    Step closeSource (2*R+4) H A (Function.update H 78 0)
      (Function.update A 78 (ZeroPadding.pad R (body++[false]))) := by
  have first:=terminate_run R body H A hh ha
  have last:=PhysicalRewindInto.run R (31 : Fin 256) 78 (by decide)
    (Function.update H 78 (body.length+1)) (Function.update A 78 (ZeroPadding.pad R (body++[false])))
    (by simpa using hw) (by simpa using hR) (by simpa using hfit)
  have he : Function.update (Function.update H 78 (body.length+1)) 78 0=Function.update H 78 0 := by
    funext i;by_cases hi : i=78 <;>simp [Function.update,hi]
  have h:=first.seq (last.congr he rfl)
  simpa only [closeSource,show 1+1+(2*R+2)=2*R+4 by omega] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
