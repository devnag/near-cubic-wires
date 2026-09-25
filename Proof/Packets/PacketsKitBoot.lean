import Proof.Packets.ArithmeticGuard
import Proof.Packets.PacketsDock
import Proof.Packets.PacketsPolyKit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.KitBoot
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-- Reserve generator tape `j` sits at `0` (template C), `2` (template w), else `3 + j`. -/
def resSlots (j : Fin 48) : Fin 97 :=
  if j.val = 0 then ⟨0, by omega⟩ else if j.val = 1 then ⟨2, by omega⟩ else ⟨3 + j.val, by omega⟩

/-- Cold arena tape `j` sits at `47` (= reserve tape 44, `1^R`), `1` (second template C), else `51 + j`. -/
def arenaSlots (j : Fin 46) : Fin 97 :=
  if j.val = 32 then ⟨47, by omega⟩ else if j.val = 35 then ⟨1, by omega⟩ else ⟨51 + j.val, by omega⟩

theorem resSlots_injective : Function.Injective resSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  unfold resSlots at hv
  apply Fin.ext
  split_ifs at hv <;> simp_all <;> omega

theorem arenaSlots_injective : Function.Injective arenaSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  unfold arenaSlots at hv
  apply Fin.ext
  split_ifs at hv <;> simp_all <;> omega

def machine := Composition.machine (RecoveryFocus.machine resSlots Theorem25Completion.CycleCommonReserve.machine)
  (RecoveryFocus.machine arenaSlots ArithmeticCold.machine)

def cost (C w : ℕ) : ℕ :=
  Theorem25Completion.CycleCommonReserve.budget C w + 1 + 11 * Theorem25Completion.CycleCommonReserve.reserve C w

/-- The entry bank: two templates of `C`, one of `w`, everything else empty. -/
def entry (C w : ℕ) (i : Fin 97) : List Bool :=
  if i.val = 0 ∨ i.val = 1 then UnaryTemplate.tape C else if i.val = 2 then UnaryTemplate.tape w else []

/-- Where arena tape `j < 34` lands. -/
def outSlot (j : Fin 34) : Fin 97 := arenaSlots (j.castAdd 12)

theorem reserve_eq (C w : ℕ) : Theorem25Completion.CycleCommonReserve.reserve C w = PolyKit.reserve C w := by
  unfold Theorem25Completion.CycleCommonReserve.reserve PolyKit.reserve Theorem25Completion.CycleBounds.commonReserve
  rfl

theorem resSlots_val (k : Fin 48) :
    (resSlots k).val = if k.val = 0 then 0 else if k.val = 1 then 2 else 3 + k.val := by
  unfold resSlots; split_ifs <;> rfl

theorem arenaSlots_val (j : Fin 46) :
    (arenaSlots j).val = if j.val = 32 then 47 else if j.val = 35 then 1 else 51 + j.val := by
  unfold arenaSlots; split_ifs <;> rfl

theorem arena_input_other (C R : ℕ) (j : Fin 46) (h32 : j.val ≠ 32) (h35 : j.val ≠ 35) :
    ArithmeticCold.input C R j = [] := by
  fin_cases j <;> first | rfl | (exfalso; simp_all)

theorem entry_high (C w : ℕ) (i : Fin 97) (h : 3 ≤ i.val) : entry C w i = [] := by
  unfold entry
  rw [if_neg (by omega), if_neg (by omega)]

theorem arena_slot_other (j : Fin 46) (h32 : j.val ≠ 32) (h35 : j.val ≠ 35) :
    (arenaSlots j).val = 51 + j.val := by
  unfold arenaSlots
  rw [if_neg h32, if_neg h35]

theorem arena_input_32 (C R : ℕ) : ArithmeticCold.input C R 32 = List.replicate R true := rfl

theorem arena_input_35 (C R : ℕ) : ArithmeticCold.input C R 35 = UnaryTemplate.tape C := rfl

/-- **KitBoot.** From the two templates, one fixed machine builds the reusable arena. -/
theorem run (C w : ℕ) :
    ∃ (H : Fin 97 → ℕ) (A : Fin 97 → List Bool), Step machine (cost C w) (fun _ => 0) (entry C w) H A ∧
      ∀ j : Fin 34, A (outSlot j) = ReusableArithmetic.state C (PolyKit.reserve C w) [] [] j ∧
        H (outSlot j) = ReusableArithmetic.heads j := by
  -- the reserve generator
  obtain ⟨H1, A1, s1, o1, k1⟩ := Dock.lift (Theorem25Completion.CycleCommonReserve.run C w) resSlots
    resSlots_injective (fun _ => 0) (fun _ => 0) (entry C w) (by
      intro j
      refine ⟨rfl, ?_⟩
      rw [ZeroPadding.pad_zero]
      unfold resSlots entry Theorem25Completion.CycleCommonReserve.input
      split_ifs <;> simp_all <;> omega)
  -- the cold arena
  obtain ⟨H2, A2, s2, o2, k2⟩ := Dock.lift (ArithmeticCold.run_common C w) arenaSlots
    arenaSlots_injective (fun _ => 0) H1 A1 (by
      intro j
      rw [ZeroPadding.pad_zero]
      by_cases h32 : j.val = 32
      · have hj : j = 32 := Fin.ext h32
        have hs : arenaSlots j = resSlots 44 := by
          apply Fin.ext; simp [arenaSlots, resSlots, h32]
        rw [hs, (o1 _).1, (o1 _).2, ZeroPadding.pad_zero, Theorem25Completion.CycleCommonReserve.raw_reserve,
          hj, arena_input_32]
        exact ⟨rfl, rfl⟩
      · have hout : ∀ k, resSlots k ≠ arenaSlots j := by
          intro k hk
          have hv := congrArg Fin.val hk
          rw [resSlots_val, arenaSlots_val] at hv
          split_ifs at hv <;> omega
        rw [(k1 _ hout).1, (k1 _ hout).2]
        refine ⟨rfl, ?_⟩
        by_cases h35 : j.val = 35
        · have hj : j = 35 := Fin.ext h35
          have hs : arenaSlots j = ⟨1, by omega⟩ := by
            apply Fin.ext; simp [arenaSlots, h35]
          rw [hs, hj, arena_input_35]
          unfold entry
          simp
        · rw [arena_input_other C _ j h32 h35, entry_high C w _ (by rw [arena_slot_other j h32 h35]; omega)])
  refine ⟨H2, A2, s1.seq s2, fun j => ?_⟩
  have hj := o2 (j.castAdd 12)
  unfold outSlot
  rw [hj.1, hj.2, ZeroPadding.pad_zero]
  have hc := ArithmeticCold.common_core C w j
  rw [reserve_eq] at hc
  exact ⟨hc, ArithmeticCold.heads_core j⟩

end
end NearCubicWires.PacketsConstruction.KitBoot
