import Proof.Packets.PacketsXVectorLiteralProgram

/-! An explicit fixed polynomial/exponential envelope for the complete
literal-vector and whole-coordinate program. The degree and coefficient are
fixed before the later choice of the paper's large load parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.RepairOrdinary
open Theorem25Completion.CycleBounds
noncomputable section

theorem literal_delta_reserve_square (C w : Nat) (hw : 3≤w) :
    literalDeltaFuel C w≤(commonReserve C w)^2 := by
  calc
    literalDeltaFuel C w=(C+1)^6*2^(42+8*w) := by unfold literalDeltaFuel;rw [pow_add];ring
    _≤(C+1)^8*2^(32+16*w) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 1≤C+1) (by decide : 6≤8))
        (Nat.pow_le_pow_right (by decide : 1≤(2 : Nat)) (by omega))
    _=(commonReserve C w)^2 := by
      unfold commonReserve
      rw [pow_add,show 16*w=(8*w)*2 by omega,pow_mul 2 (8*w) 2]
      norm_num
      ring

theorem literal_coordinate_reserve_cube (C w : Nat) :
    4398046511104*(C+1)^9*2^(17*w)≤(commonReserve C w)^3 := by
  calc
    4398046511104*(C+1)^9*2^(17*w)≤2^48*(C+1)^12*2^(24*w) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by norm_num : 4398046511104≤2^48)
        (Nat.pow_le_pow_right (by omega : 1≤C+1) (by decide : 9≤12)))
        (Nat.pow_le_pow_right (by decide : 1≤(2 : Nat)) (by omega))
    _=(commonReserve C w)^3 := by
      unfold commonReserve
      rw [show 24*w=(8*w)*3 by omega,pow_mul 2 (8*w) 3]
      norm_num
      ring

theorem literal_program_cost (C w M root depth : Nat) (hw : 3≤w)
    (hM : M+1≤C+1) (hd : depth≤C) (hroot : root≤commonReserve C w) :
    literalProgramFuel C w M root depth≤2^100*(C+1)^20*2^(40*w) := by
  let R:=commonReserve C w
  let T:=R+1
  have reserve : C+2≤R:=LiteralCacheReuse.reserve_width C w
  have hR : 1≤R := by omega
  have hT : 1≤T := by dsimp [T];omega
  have hRT : R≤T := by dsimp [T];omega
  have hN : M+1≤T := by dsimp [T];omega
  have hdepth : depth≤T := by dsimp [T];omega
  have hrootT : root≤T := hroot.trans hRT
  have hdelta : literalDeltaFuel C w≤T^2 :=
    (literal_delta_reserve_square C w hw).trans (Nat.pow_le_pow_left hRT 2)
  have hprovider : WindowProvider.levelUniformBudget C w≤T^2 := by
    apply le_trans (b:=literalDeltaFuel C w) _ hdelta
    unfold WindowProvider.levelUniformBudget literalDeltaFuel
    gcongr <;> norm_num
  have hcoord : 4398046511104*(C+1)^9*2^(17*w)≤T^3 :=
    (literal_coordinate_reserve_cube C w).trans (Nat.pow_le_pow_left hRT 3)
  have major : literalProgramFuel C w M root depth≤
      T*(oneLevelFuel T (T^2) T (uniformPrepareBudget T T T (T^2))+2*T+6)+4+
        (2*T+7+T*(2*PacketBank.lookupBudget T T+(4*T+6+T^3)+10+2*T+6)+3) := by
    unfold literalProgramFuel literalLevelFuel literalCoordinatesFuel literalCoordinateFuel
      oneLevelFuel allParentsFuel parentBodyFuel parentChildrenFuel uniformPrepareBudget VectorTransfer.budget PacketBank.lookupBudget
    gcongr
    omega
  have coarse : T*(oneLevelFuel T (T^2) T (uniformPrepareBudget T T T (T^2))+2*T+6)+4+
      (2*T+7+T*(2*PacketBank.lookupBudget T T+(4*T+6+T^3)+10+2*T+6)+3)≤4096*T^5 := by
    have h1 : T≤T^5 := by simpa using Nat.pow_le_pow_right hT (show 1≤5 by decide)
    have h2 : T^2≤T^5 := Nat.pow_le_pow_right hT (by decide)
    have h3 : T^3≤T^5 := Nat.pow_le_pow_right hT (by decide)
    have h4 : T^4≤T^5 := Nat.pow_le_pow_right hT (by decide)
    have h5 : 1≤T^5 := Nat.one_le_pow _ _ hT
    unfold oneLevelFuel allParentsFuel parentBodyFuel parentChildrenFuel uniformPrepareBudget VectorTransfer.budget PacketBank.lookupBudget
    ring_nf
    omega
  have htwo : T≤2*R := by dsimp [T];omega
  calc
    literalProgramFuel C w M root depth≤4096*T^5 := major.trans coarse
    _≤4096*(2*R)^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htwo 5)
    _=2^97*(C+1)^20*2^(40*w) := by
      dsimp only [R]
      unfold commonReserve
      rw [show 40*w=(8*w)*5 by omega,pow_mul 2 (8*w) 5]
      norm_num
      ring
    _≤2^100*(C+1)^20*2^(40*w) := by gcongr <;> norm_num

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
