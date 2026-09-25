import Proof.MachineModel.BankExecution
import Proof.MachineModel.BankFields

/-! Physical raw incidence production, paid cursor return, and the EXISTING
polynomial consumer. All other native fields are explicit caller-produced
inputs. The separate zero-polynomial branch is not supplied here. -/
namespace NearCubicWires.ExtIncidence.BankConsumer
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 116 := i.castAdd 3
theorem old_injective : Function.Injective old := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 116=>k.val) h)
theorem old_ne (i : Fin 113) (k : Fin 116) (hk : 113 ≤ k.val) : old i≠k := by
  intro he
  have hv:=congrArg Fin.val he
  change i.val=k.val at hv
  omega


end NearCubicWires.ExtIncidence.BankConsumer
