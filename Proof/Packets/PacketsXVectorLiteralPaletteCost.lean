import Proof.Packets.PacketsXVectorLiteralPaletteProgram
import Proof.Packets.PacketsXVectorLiteralInitializationCost

/-! A fixed outer reserve and paid fanout envelope, chosen independently
of the later load parameter. This is a local vector-visit cost. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.RepairOrdinary
open Theorem25Completion.CycleBounds
noncomputable section

def paletteReserve (C w : Nat) := 2^102*(C+1)^20*2^(40*w)

theorem palette_reserve_min (C w : Nat) : 16 ≤ paletteReserve C w := by
  have hp : 1 ≤ (C+1)^20 := Nat.one_le_pow _ _ (by omega)
  have he : 1 ≤ 2^(40*w) := Nat.one_le_pow _ _ (by decide)
  unfold paletteReserve
  calc
    16 ≤ 2^102*1*1 := by norm_num
    _ ≤ 2^102*(C+1)^20*2^(40*w) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) he

theorem palette_reserve_common (C w : Nat) : commonReserve C w+3 ≤ paletteReserve C w := by
  let B:=(C+1)^20*2^(40*w)
  have hb : 1 ≤ B := by
    dsimp only [B]
    exact Nat.mul_pos (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by decide))
  have hr : commonReserve C w ≤ 2^100*B := by
    unfold commonReserve
    dsimp only [B]
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (by norm_num : 65536 ≤ 2^100)
        (Nat.pow_le_pow_right (by omega : 1 ≤ C+1) (by decide : 4 ≤ 20)))
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) (by omega : 8*w ≤ 40*w))
  change commonReserve C w+3 ≤ 2^102*(C+1)^20*2^(40*w)
  rw [Nat.mul_assoc]
  change commonReserve C w+3 ≤ 2^102*B
  norm_num at *
  omega

theorem palette_reserve_width (C w : Nat) : 2*C+5 ≤ paletteReserve C w := by
  have hsmall : 2*C+5 ≤ commonReserve C w := by
    have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
    have hp : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) _
    unfold commonReserve
    nlinarith [Nat.mul_le_mul_left (65536*(C+1)^4) he]
  have hs:=palette_reserve_common C w
  omega

theorem palette_reserve_execution (C w M root depth : Nat) (hw : 3 ≤ w)
    (hM : M ≤ C) (hd : depth ≤ C) (hroot : root ≤ commonReserve C w) :
    literalInitializedFuel C w M root depth+2 ≤ paletteReserve C w := by
  let B:=(C+1)^20*2^(40*w)
  have hb : 1 ≤ B := by
    dsimp only [B]
    exact Nat.mul_pos (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by decide))
  have h:=literal_initialized_program_cost C w M root depth hw hM hd hroot
  rw [Nat.mul_assoc] at h
  change literalInitializedFuel C w M root depth ≤ 2^101*B at h
  unfold paletteReserve
  rw [Nat.mul_assoc]
  change literalInitializedFuel C w M root depth+2 ≤ 2^102*B
  norm_num at *
  omega

theorem literal_palette_program_cost (C w M root depth : Nat) (hw : 3 ≤ w)
    (hM : M ≤ C) (hd : depth ≤ C) (hroot : root ≤ commonReserve C w) :
    literalPaletteFuel C w M root depth (paletteReserve C w) ≤ 2^104*(C+1)^20*2^(40*w) := by
  have h:=palette_reserve_execution C w M root depth hw hM hd hroot
  have hs:=palette_reserve_min C w
  calc
    literalPaletteFuel C w M root depth (paletteReserve C w) ≤ 4*paletteReserve C w := by
      unfold literalPaletteFuel;omega
    _=2^104*(C+1)^20*2^(40*w) := by unfold paletteReserve;norm_num;ring

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
