import Proof.Packets.PacketsXVectorLiteralPalettePadding

/-! Exact master-word updates through the palette's nested tape layout. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
noncomputable section

theorem palette_update_master (palette : Fin 15 → List Bool) (S : Nat)
    (work : Fin 299 → List Bool) (j : Fin 15) (word : List Bool) :
    Function.update (paletteData palette S work) (j.castAdd 301) word =
      paletteData (Function.update palette j word) S work := by
  change Function.update (paletteData palette S work) ((j.castAdd 300).castAdd 1) word=_
  unfold paletteData
  rw [PhysicalAppendUpdate.left,PhysicalAppendUpdate.left]

theorem walk_palette_update_master (walk : Fin 15 → List Bool) (palette : Fin 15 → List Bool)
    (S : Nat) (work : Fin 299 → List Bool) (j : Fin 15) (word : List Bool) :
    Function.update
      (Fin.addCases (m:=15) (n:=316) (motive:=fun _=>List Bool) walk (paletteData palette S work))
      ((j.castAdd 301).natAdd 15) word =
      Fin.addCases (m:=15) (n:=316) (motive:=fun _=>List Bool) walk
        (paletteData (Function.update palette j word) S work) := by
  rw [PhysicalAppendUpdate.right,palette_update_master]

def seedPalette (R : Nat) (palette : Fin 15 → List Bool) (fields : Fin 3 → List Bool) :=
  Function.update (Function.update (Function.update palette 6 (ZeroPadding.pad R (fields 0)))
    7 (ZeroPadding.pad R (fields 1))) 8 (ZeroPadding.pad R (fields 2))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
