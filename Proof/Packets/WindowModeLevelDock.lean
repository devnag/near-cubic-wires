import Proof.Packets.ModeLevelRaw
import Proof.Packets.WindowProviderPorts

/-! Physical level derivation in the fixed provider arena. The actual row
successor tag is retained; no standalone raw-level word is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def modeLevelPorts : Fin 5→Fin 256 := ![187,159,176,32,33]
theorem modeLevel_injective : Function.Injective modeLevelPorts := by decide
noncomputable def makeModeLevel := RecoveryFocus.machine modeLevelPorts ModeLevelRaw.machine
def modeLevelOutput (R level : Nat) (A : Fin 256→List Bool) :=
  Function.update (Function.update A 159 (ZeroPadding.pad R (List.replicate level true)))
    176 (List.replicate R false)

theorem make_mode_level_run (R level : Nat) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀i,H (modeLevelPorts i)=0)
    (htag : A 187=WindowSeed.source R (level+1))
    (hraw : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hold : (A 159).length≤R) (htemp : (A 176).length≤R) (hcap : level+2≤R) :
    Step makeModeLevel (ModeLevelRaw.budget R level) H A H (modeLevelOutput R level A) := by
  apply PhysicalFocusBoundary.focus (ModeLevelRaw.run R level (A 159) (A 176) hold htemp hcap)
    modeLevelPorts modeLevel_injective H H A _
  · intro i;exact (hH i).symm
  · intro i;fin_cases i <;>first | rfl | exact htag.symm | exact hraw.symm | exact hlog.symm
  · intro i;exact (hH i).symm
  · intro i;fin_cases i <;>simp [ModeLevelRaw.A,ModeLevelRaw.zero,modeLevelOutput,modeLevelPorts,htag,hraw,hlog]
  · intro i away
    have h159 : i≠159:=by intro he;subst i;exact away 1 rfl
    have h176 : i≠176:=by intro he;subst i;exact away 2 rfl
    exact ⟨rfl,by simp only [modeLevelOutput,Function.update_of_ne h159,Function.update_of_ne h176]⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
