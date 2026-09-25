import Proof.Packets.PhysicalBoundedLeftRewind
import Proof.Rows.PhysicalFocusBoundary

/-! Paid rewind by a retained capacity driver in an arbitrary ambient bank. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRewindInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def slots {t : Nat} (width source : Fin t) : Fin 2→Fin t := ![width,source]
noncomputable def machine {t : Nat} (width source : Fin t) :=
  RecoveryFocus.machine (slots width source) Completion.PhysicalBoundedLeftRewind.machine

theorem run {t : Nat} (R : Nat) (width source : Fin t) (hne : width≠source)
    (H : Fin t→Nat) (A : Fin t→List Bool) (hw : H width=1) (ha : A width=UnaryTemplate.tape R)
    (hpos : H source≤R) :
    Step (machine width source) (2*R+2) H A (Function.update H source 0) A := by
  obtain ⟨r,hr,hf,hs⟩:=Completion.PhysicalBoundedLeftRewind.run R (H source) (A source) hpos
  have small : Step Completion.PhysicalBoundedLeftRewind.machine (2*R+2)
      (![1,H source]) (![UnaryTemplate.tape R,A source]) (![1,0]) (![UnaryTemplate.tape R,A source]) :=
    ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le⟩
  have hi : Function.Injective (slots width source) := by
    intro i j he
    fin_cases i <;>fin_cases j
    · rfl
    · exact False.elim (hne he)
    · exact False.elim (hne he.symm)
    · rfl
  apply PhysicalFocusBoundary.focus small (slots width source) hi H (Function.update H source 0) A A
  · intro i;fin_cases i <;>simp [slots,hw]
  · intro i;fin_cases i <;>simp [slots,ha]
  · intro i;fin_cases i <;>simp [slots,Function.update,hne,hw]
  · intro i;fin_cases i <;>simp [slots,ha]
  · intro i away
    have hn : i≠source := by intro he;subst i;exact away 1 rfl
    exact ⟨by simp [Function.update,hn],rfl⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRewindInto
