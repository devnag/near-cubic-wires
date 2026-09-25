import Proof.Packets.PacketsXWalkLiteralSeedReady
import Proof.Packets.PhysicalPrepend

/-! The walk prefix, palette arena, and transcript have one literal tape
layout across the decoder and polynomial collector. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace Theorem25Completion.WalkPaletteAssociativity

theorem append {α : Sort*} (walk : Fin 15 → α) (palette : Fin 316 → α) (extra : Fin 1 → α) :
    Fin.addCases (m:=331) (n:=1) (motive:=fun _=>α)
      (Fin.addCases (m:=15) (n:=316) (motive:=fun _=>α) walk palette) extra =
    Fin.addCases (m:=15) (n:=317) (motive:=fun _=>α) walk
      (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>α) palette extra) := by
  funext i
  refine Fin.addCases (m:=331) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=15) (n:=316) (fun k=>?_) (fun k=>?_) j
    · simp only [Fin.addCases_left]
      change walk k=Fin.addCases (m:=15) (n:=317) (motive:=fun _=>α) walk
        (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>α) palette extra) (k.castAdd 317)
      simp only [Fin.addCases_left]
    · simp only [Fin.addCases_left,Fin.addCases_right]
      change palette k=Fin.addCases (m:=15) (n:=317) (motive:=fun _=>α) walk
        (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>α) palette extra) ((k.castAdd 1).natAdd 15)
      simp only [Fin.addCases_right,Fin.addCases_left]
  · fin_cases j
    rfl

end Theorem25Completion.WalkPaletteAssociativity
