import Proof.Packets.PacketsLowerRun3

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerBudget
open NearCubicWires Theorem25Completion.CycleBounds
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer

theorem outer_budget (C w : ℕ) (P : Ring.Poly ℕ) (hw : 1 ≤ w) (hc : P.length ≤ 2 ^ w) :
    PacketOuterNormalize.budget C (commonReserve C w) P ≤ 11 * commonReserve C w := by
  have h := normalized_addition_reserve C w [] (P.map (NormalizedFiniteTransport.maskNat C)) (by simp)
    (SubstitutionCensus.mask_width C P) (by simp) (by simpa only [List.length_map] using hc) hw
  have hr := (Theorem25Completion.CycleDenseAtomCost.reserve_small C w).1
  unfold PacketOuterNormalize.budget ReusableArithmetic.budget
  omega

theorem substitution_budget (C R M : ℕ) :
    SubstitutionCall.coldBudget C R M ≤ 256 * (M + 1) * (C + 1) * (R + 1) ^ 2 := by
  unfold SubstitutionCall.coldBudget SubstitutionCall.totalBudget SubstitutionCall.prepareBudget
    PhysicalProductSeek.budget SubstitutionOuter.budget SubstitutionOuter.bodyBudget
    SubstitutionCall.finishBudget
  ring_nf
  omega

theorem rewound_budget (C w : ℕ) (P Q : Ring.Poly ℕ) (hw : 1 ≤ w)
    (hp : P.length ≤ 2 ^ w) (hq : Q.length ≤ 2 ^ w) (hn : (Ring.norm Q).length ≤ 2 ^ w) :
    MajorityComplete.PacketRun.budget C (commonReserve C w) P Q + 1 + 2 * commonReserve C w + 2 ≤
      2 ^ 44 * (C + 1) ^ 9 * 2 ^ (17 * w) := by
  set R := commonReserve C w with hRdef
  have hs := substitution_budget C R P.length
  have ho := outer_budget C w Q hw hq
  have hn' := PacketNativeMeaning.serializer_reserve C w (Ring.norm Q).length hn
  have hpR : R + 1 ≤ (P.length + 1) * (C + 1) * (R + 1) ^ 2 := by
    have hp1 : 1 ≤ (P.length + 1) * (C + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hpow : R + 1 ≤ (R + 1) ^ 2 := Nat.le_self_pow (by decide) _
    have hm := Nat.mul_le_mul_right ((R + 1) ^ 2) hp1
    nlinarith only [hm, hpow]
  have hb : MajorityComplete.PacketRun.budget C R P Q + 1 + 2 * R + 2 ≤
      512 * (P.length + 1) * (C + 1) * (R + 1) ^ 2 := by
    change PacketOuterNormalize.budget C R Q ≤ 11 * R at ho
    change (Ring.norm Q).length * (C ^ 2 + 8 * C + 9) + 9 ≤ R at hn'
    unfold MajorityComplete.PacketRun.budget
    nlinarith only [hs, ho, hn', hpR]
  have hP : P.length + 1 ≤ 2 * 2 ^ w := by have h := Nat.one_le_pow w 2 (by decide); omega
  have hR : R + 1 ≤ 2 * R := by
    have h := (Theorem25Completion.CycleDenseAtomCost.reserve_small C w).1
    rw [hRdef]; omega
  calc
    _ ≤ 512 * (P.length + 1) * (C + 1) * (R + 1) ^ 2 := hb
    _ ≤ 512 * (2 * 2 ^ w) * (C + 1) * (2 * R) ^ 2 := by gcongr
    _ = 2 ^ 44 * (C + 1) ^ 9 * 2 ^ (17 * w) := by
      rw [hRdef]
      unfold commonReserve
      have hex : 2 ^ (17 * w) = 2 ^ w * (2 ^ (8 * w)) ^ 2 := by
        rw [← Nat.pow_mul, ← Nat.pow_add]
        congr 1
        omega
      rw [hex]
      ring

theorem prepare_budget (C R count : ℕ) (hc : count ≤ C) :
    MajorityComplete.PacketAtoms.budget C R count + 1 + (4 * R + 5) + 1 ≤ 512 * (C + 1) ^ 2 * (R + 1) := by
  have hm : MajorityComplete.PacketAtoms.budget C R count ≤ MajorityComplete.PacketAtoms.budget C R C := by
    unfold MajorityComplete.PacketAtoms.budget IdentityCodeCache.budget IdentityCodeLoop.budget
      AddressedAtomCold.budget AddressedAtomMaterialize.budget AddressedAtomProgram.budget
      AddressedAtomProgram.bodyBudget DenseAtomInitialize.budget
    gcongr
  apply (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hm 1) (4 * R + 5)) 1).trans
  unfold MajorityComplete.PacketAtoms.budget IdentityCodeCache.budget IdentityCodeLoop.budget
    AddressedAtomCold.budget AddressedAtomMaterialize.budget AddressedAtomProgram.budget
    AddressedAtomProgram.bodyBudget DenseAtomInitialize.budget
  ring_nf
  omega

theorem prepare_reserve_budget (C w count : ℕ) (hc : count ≤ C) :
    MajorityComplete.PacketAtoms.budget C (commonReserve C w) count + 1 + (4 * commonReserve C w + 5) + 1 ≤
      2 ^ 26 * (C + 1) ^ 6 * 2 ^ (8 * w) := by
  have hr : commonReserve C w + 1 ≤ 2 * commonReserve C w := by
    have h := (Theorem25Completion.CycleDenseAtomCost.reserve_small C w).1
    omega
  calc
    _ ≤ 512 * (C + 1) ^ 2 * (commonReserve C w + 1) := prepare_budget C _ count hc
    _ ≤ 512 * (C + 1) ^ 2 * (2 * commonReserve C w) := by gcongr
    _ = 2 ^ 26 * (C + 1) ^ 6 * 2 ^ (8 * w) := by unfold commonReserve; ring

/-- **The join's budget, uniformly.** -/
theorem join_budget (C w count : ℕ) (P Q : Ring.Poly ℕ) (hc : count ≤ C) (hw : 1 ≤ w)
    (hp : P.length ≤ 2 ^ w) (hq : Q.length ≤ 2 ^ w) (hn : (Ring.norm Q).length ≤ 2 ^ w) :
    MajorityComplete.PacketAtomsJoin.budget C (commonReserve C w) count P Q ≤
      2 ^ 45 * (C + 1) ^ 9 * 2 ^ (17 * w) := by
  have ha := prepare_reserve_budget C w count hc
  have hb := rewound_budget C w P Q hw hp hq hn
  have ha' : MajorityComplete.PacketAtoms.budget C (commonReserve C w) count + 1 + (4 * commonReserve C w + 5) + 1 ≤
      2 ^ 26 * (C + 1) ^ 9 * 2 ^ (17 * w) := by
    apply ha.trans
    gcongr <;> omega
  unfold MajorityComplete.PacketAtomsJoin.budget
  norm_num at ha' hb ⊢
  nlinarith only [ha', hb]

end NearCubicWires.PacketsConstruction.LowerBudget
