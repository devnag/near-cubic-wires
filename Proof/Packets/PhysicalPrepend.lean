import Proof.Rows.PhysicalFocusBoundary

/-! Preserve a fixed prefix of resident tapes around an actual execution. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalPrepend
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def machine {t states : Nat} (e : Nat) (program : Machine t states) :=
  RecoveryFocus.machine (fun i : Fin t=>i.natAdd e) program

theorem run {t states fuel : Nat} {program : Machine t states}
    {hin hout : Fin t → Nat} {tin tout : Fin t → List Bool}
    (step : Step program fuel hin tin hout tout) {e : Nat}
    (prefixHeads : Fin e → Nat) (prefixData : Fin e → List Bool) :
    Step (machine e program) fuel
      (Fin.addCases (m:=e) (n:=t) (motive:=fun _=>Nat) prefixHeads hin)
      (Fin.addCases (m:=e) (n:=t) (motive:=fun _=>List Bool) prefixData tin)
      (Fin.addCases (m:=e) (n:=t) (motive:=fun _=>Nat) prefixHeads hout)
      (Fin.addCases (m:=e) (n:=t) (motive:=fun _=>List Bool) prefixData tout) := by
  have inj : Function.Injective (fun i : Fin t=>i.natAdd e) := by
    intro i j he
    apply Fin.ext
    have h:=congrArg (fun z : Fin (e+t)=>z.val) he
    dsimp at h
    omega
  apply PhysicalFocusBoundary.focus step (fun i : Fin t=>i.natAdd e) inj
  · intro i;simp only [Fin.addCases_right]
  · intro i;simp only [Fin.addCases_right]
  · intro i;simp only [Fin.addCases_right]
  · intro i;simp only [Fin.addCases_right]
  · intro i
    refine Fin.addCases (m:=e) (n:=t) (fun j=>?_) (fun j=>?_) i
    · intro _;constructor <;>simp only [Fin.addCases_left]
    · intro away;exact False.elim (away j rfl)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalPrepend
