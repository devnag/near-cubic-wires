import Proof.Packets.PacketsXVectorLiteralPaletteBoot

/-! Physically allocated source masters are accepted at their existing
padding. The vector destinations and outside driver are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding CloseoutRowsModeCache
noncomputable section

def paletteMasterCaps (R : Nat) (i : Fin 316) := if i.val<15 then R else 0
def paddedPalette (C R M root depth : Nat) (p : Parameters) (i : Fin 15) :=
  ZeroPadding.pad R (coldPalette C R M root depth p i)

theorem palette_pad_data (R S : Nat) (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) :
    (fun i=>ZeroPadding.pad (paletteMasterCaps R i) (paletteData palette S work i)) =
      paletteData (fun j=>ZeroPadding.pad R (palette j)) S work := by
  funext i
  refine Fin.addCases (m:=315) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=15) (n:=300) (fun k=>?_) (fun k=>?_) j
    · simp only [paletteData,Fin.addCases_left,paletteMasterCaps,Fin.val_castAdd,
        show k.val<15 from k.isLt,if_true]
    · simp only [paletteData,Fin.addCases_left,Fin.addCases_right,paletteMasterCaps,
        Fin.val_castAdd,Fin.val_natAdd,show ¬15+k.val<15 by omega,if_false,ZeroPadding.pad_zero]
  · simp only [paletteData,Fin.addCases_right,paletteMasterCaps,Fin.val_natAdd,
      show ¬315+j.val<15 by omega,if_false,ZeroPadding.pad_zero]

theorem palette_pad_input (R S : Nat) (palette : Fin 15 → List Bool) :
    (fun i=>ZeroPadding.pad (paletteMasterCaps R i) (NativeFanout.input (m:=299) palette S i)) =
      NativeFanout.input (m:=299) (fun j=>ZeroPadding.pad R (palette j)) S := by
  funext i
  refine Fin.addCases (m:=315) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=15) (n:=300) (fun k=>?_) (fun k=>?_) j
    · simp only [NativeFanout.input,Fin.addCases_left,paletteMasterCaps,Fin.val_castAdd,
        show k.val<15 from k.isLt,if_true]
    · simp only [NativeFanout.input,Fin.addCases_left,Fin.addCases_right,paletteMasterCaps,
        Fin.val_castAdd,Fin.val_natAdd,show ¬15+k.val<15 by omega,if_false,ZeroPadding.pad_zero]
  · simp only [NativeFanout.input,Fin.addCases_right,paletteMasterCaps,Fin.val_natAdd,
      show ¬315+j.val<15 by omega,if_false,ZeroPadding.pad_zero]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
