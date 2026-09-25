import Proof.Packets.PacketsXVectorLiteralInitializedProgram
import Proof.Packets.PacketsXVectorLiteralProgramCost

/-! Fixed runtime envelope including physical bank and counter production. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.RepairOrdinary
open Theorem25Completion.CycleBounds
noncomputable section

theorem literal_initialization_cost (C w M : Nat) (hM : M≤C) :
    initializeLiteralFuel C (commonReserve C w) M+1≤2^100*(C+1)^20*2^(40*w) := by
  let R:=commonReserve C w
  let T:=R+1
  have reserve : C+2≤R:=LiteralCacheReuse.reserve_width C w
  have hR : 1≤R := by omega
  have hT : 1≤T := by dsimp [T];omega
  have hRT : R≤T := by dsimp [T];omega
  have hC : C≤T := by dsimp [T];omega
  have hMT : M≤T := by omega
  have hN : M+1≤T := by dsimp [T];omega
  have hwidth : Completion.SourceDigitWidth.budget (2*M)≤T := by
    have hb:=Completion.SourceDigitWidth.budget_bound (2*M)
    have cap : Completion.SourceDigitWidth.capacity (2*M)≤R :=
      Theorem25Completion.CycleDeltaMetadataCost.phase_width_reserve C w M hM
    omega
  have major : initializeLiteralFuel C R M+1≤
      (T*(12*T+24)+11+4)+1+
      ((8*T+4*T+(T*(2*(T+T)+5)+3)+T+30)+10*T+8*T+56+
      ((T*(12*T+24)+11)+(4*(0*(2*T+5)+3)+8*T+19)+4)+
      (T*(12*T+24)+11))+1 := by
    unfold initializeLiteralFuel VectorNumericArena.denseBudget VectorNumericArena.initializeBudget
      VectorNumericArena.phaseBudget VectorTerminalBank.budget PhysicalZeroBank.budget
      PacketBank.lookupBudget UnaryAddCount.budget
    gcongr
  have coarse : (T*(12*T+24)+11+4)+1+
      ((8*T+4*T+(T*(2*(T+T)+5)+3)+T+30)+10*T+8*T+56+
      ((T*(12*T+24)+11)+(4*(0*(2*T+5)+3)+8*T+19)+4)+
      (T*(12*T+24)+11))+1≤4096*T^5 := by
    have h1 : T≤T^5 := by simpa using Nat.pow_le_pow_right hT (show 1≤5 by decide)
    have h2 : T^2≤T^5 := Nat.pow_le_pow_right hT (by decide)
    have h5 : 1≤T^5 := Nat.one_le_pow _ _ hT
    ring_nf
    omega
  have htwo : T≤2*R := by dsimp [T];omega
  calc
    initializeLiteralFuel C R M+1≤4096*T^5 := major.trans coarse
    _≤4096*(2*R)^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htwo 5)
    _=2^97*(C+1)^20*2^(40*w) := by
      dsimp only [R]
      unfold commonReserve
      rw [show 40*w=(8*w)*5 by omega,pow_mul 2 (8*w) 5]
      norm_num
      ring
    _≤2^100*(C+1)^20*2^(40*w) := by gcongr <;> norm_num

theorem literal_initialized_program_cost (C w M root depth : Nat) (hw : 3≤w)
    (hM : M≤C) (hd : depth≤C) (hroot : root≤commonReserve C w) :
    literalInitializedFuel C w M root depth≤2^101*(C+1)^20*2^(40*w) := by
  have init:=literal_initialization_cost C w M hM
  have body:=literal_program_cost C w M root depth hw (by omega) hd hroot
  unfold literalInitializedFuel
  calc
    _≤2^100*(C+1)^20*2^(40*w)+2^100*(C+1)^20*2^(40*w) := Nat.add_le_add init body
    _=2^101*(C+1)^20*2^(40*w) := by norm_num;ring

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
