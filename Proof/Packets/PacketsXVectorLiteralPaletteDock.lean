import Proof.Packets.PacketsXVectorLiteralPaletteBoot

/-! Exact focused execution while preserving all fifteen palette masters
and the outside raw reserve and erase log. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem palette_dock_run {s fuel : Nat} (machine : Machine 299 s)
    (palette : Fin 15 → List Bool) (S : Nat) (hin hout : Fin 299 → Nat)
    (tin tout : Fin 299 → List Bool) (run : Step machine fuel hin tin hout tout) :
    Step (RecoveryFocus.machine paletteArenaSlots machine) fuel
      (paletteHeads hin) (paletteData palette S tin) (paletteHeads hout) (paletteData palette S tout) := by
  apply PhysicalFocusBoundary.focus run paletteArenaSlots palette_arena_injective
    (paletteHeads hin) (paletteHeads hout) (paletteData palette S tin) (paletteData palette S tout)
  · intro i;exact (palette_arena_heads hin i).symm
  · intro i;exact (palette_arena_data palette S tin i).symm
  · intro i;exact (palette_arena_heads hout i).symm
  · intro i;exact (palette_arena_data palette S tout i).symm
  · intro i
    refine Fin.addCases (m:=315) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=15) (n:=300) (fun k=>?_) (fun k=>?_) j
      · intro _;constructor <;>simp only [paletteHeads,paletteData,Fin.addCases_left]
      · refine Fin.addCases (m:=299) (n:=1) (fun l=>?_) (fun l=>?_) k
        · intro away;exact False.elim (away l (by apply Fin.ext;rfl))
        · intro _;constructor <;>simp only [paletteHeads,paletteData,Fin.addCases_left,Fin.addCases_right]
    · intro _;constructor <;>simp only [paletteHeads,paletteData,Fin.addCases_right]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
