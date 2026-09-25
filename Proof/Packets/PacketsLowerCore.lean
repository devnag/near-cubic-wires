import Proof.Packets.PacketsLowerWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerCore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-! ## Slot maps -/

def kbSlots (k : Fin 97) : Fin 302 := if k.val < 3 then ⟨3 + k.val, by omega⟩ else ⟨127 + k.val, by omega⟩
def raSlots (k : Fin 18) : Fin 302 :=
  if k.val = 0 then ⟨8, by omega⟩ else if k.val = 15 then ⟨7, by omega⟩
  else if k.val = 12 then ⟨278, by omega⟩ else ⟨224 + k.val, by omega⟩
def moveSlots (k : Fin 2) : Fin 302 := if k.val = 0 then ⟨289, by omega⟩ else ⟨300, by omega⟩
def lookSlots (k : Fin 6) : Fin 302 :=
  if k.val = 0 then ⟨209, by omega⟩ else if k.val = 1 then ⟨1, by omega⟩ else if k.val = 2 then ⟨288, by omega⟩
  else if k.val = 3 then ⟨289, by omega⟩ else if k.val = 4 then ⟨300, by omega⟩ else ⟨301, by omega⟩
def joinSlots (j : Fin 58) : Fin 302 :=
  if j.val < 30 then ⟨178 + j.val, by omega⟩
  else if j.val = 32 then ⟨208, by omega⟩ else if j.val = 33 then ⟨209, by omega⟩
  else if j.val = 34 then ⟨174, by omega⟩ else if j.val = 35 then ⟨211, by omega⟩
  else if j.val = 45 then ⟨6, by omega⟩ else if j.val = 57 then ⟨2, by omega⟩
  else ⟨242 + j.val, by omega⟩

theorem kbSlots_val (k : Fin 97) : (kbSlots k).val = if k.val < 3 then 3 + k.val else 127 + k.val := by
  unfold kbSlots; split_ifs <;> rfl
theorem raSlots_val (k : Fin 18) : (raSlots k).val =
    if k.val = 0 then 8 else if k.val = 15 then 7 else if k.val = 12 then 278 else 224 + k.val := by
  unfold raSlots; split_ifs <;> rfl
theorem moveSlots_val (k : Fin 2) : (moveSlots k).val = if k.val = 0 then 289 else 300 := by
  unfold moveSlots; split_ifs <;> rfl
theorem lookSlots_val (k : Fin 6) : (lookSlots k).val =
    if k.val = 0 then 209 else if k.val = 1 then 1 else if k.val = 2 then 288
    else if k.val = 3 then 289 else if k.val = 4 then 300 else 301 := by
  unfold lookSlots; split_ifs <;> rfl
theorem joinSlots_val (j : Fin 58) : (joinSlots j).val =
    if j.val < 30 then 178 + j.val else if j.val = 32 then 208 else if j.val = 33 then 209
    else if j.val = 34 then 174 else if j.val = 35 then 211 else if j.val = 45 then 6
    else if j.val = 57 then 2 else 242 + j.val := by
  unfold joinSlots; split_ifs <;> rfl

theorem kbSlots_injective : Function.Injective kbSlots := by
  intro i j h; have hv := congrArg Fin.val h; rw [kbSlots_val, kbSlots_val] at hv
  apply Fin.ext; split_ifs at hv <;> omega
theorem raSlots_injective : Function.Injective raSlots := by
  intro i j h; have hv := congrArg Fin.val h; rw [raSlots_val, raSlots_val] at hv
  apply Fin.ext; split_ifs at hv <;> omega
theorem moveSlots_injective : Function.Injective moveSlots := by
  intro i j h; have hv := congrArg Fin.val h; rw [moveSlots_val, moveSlots_val] at hv
  apply Fin.ext; split_ifs at hv <;> omega
theorem lookSlots_injective : Function.Injective lookSlots := by
  intro i j h; have hv := congrArg Fin.val h; rw [lookSlots_val, lookSlots_val] at hv
  apply Fin.ext; split_ifs at hv <;> omega
theorem joinSlots_injective : Function.Injective joinSlots := by
  intro i j h; have hv := congrArg Fin.val h; rw [joinSlots_val, joinSlots_val] at hv
  apply Fin.ext; split_ifs at hv <;> omega

/-! ## The machine -/

def rawSel (i : Fin 17) : Bool := decide (i.val = 12)

def kbStep := RecoveryFocus.machine kbSlots KitBoot.machine
def raStep := RecoveryFocus.machine raSlots (MaskedReset.machine CloseoutRowsRawAtomProducer.machine rawSel)
def moveStep (d : HeadMove) := RecoveryFocus.machine moveSlots (Completion.PhysicalDriverMoves.machine 2 d)
def lookStep := RecoveryFocus.machine lookSlots PacketBank.lookup
def joinStep := RecoveryFocus.machine joinSlots MajorityComplete.PacketAtomsJoin.machine

/-- **The F2 core machine**, fixed given the metadata machine. -/
def loadStep := Composition.machine (moveStep .right) (Composition.machine lookStep (moveStep .left))

/-! ## Non-membership in the slot images -/

theorem kbSlots_ne (i : Fin 302) (h : i.val < 3 ∨ (5 < i.val ∧ i.val < 130) ∨ 223 < i.val) :
    ∀ k, kbSlots k ≠ i := by
  intro k hk; have hv := congrArg Fin.val hk; rw [kbSlots_val] at hv; split_ifs at hv <;> omega
theorem raSlots_ne (i : Fin 302)
    (h : i.val ≠ 7 ∧ i.val ≠ 8 ∧ i.val ≠ 278 ∧ (i.val < 224 ∨ 241 < i.val)) : ∀ k, raSlots k ≠ i := by
  intro k hk; have hv := congrArg Fin.val hk; rw [raSlots_val] at hv; split_ifs at hv <;> omega
theorem moveSlots_ne (i : Fin 302) (h : i.val ≠ 289 ∧ i.val ≠ 300) : ∀ k, moveSlots k ≠ i := by
  intro k hk; have hv := congrArg Fin.val hk; rw [moveSlots_val] at hv; split_ifs at hv <;> omega
theorem lookSlots_ne (i : Fin 302)
    (h : i.val ≠ 209 ∧ i.val ≠ 1 ∧ i.val ≠ 288 ∧ i.val ≠ 289 ∧ i.val ≠ 300 ∧ i.val ≠ 301) :
    ∀ k, lookSlots k ≠ i := by
  intro k hk; have hv := congrArg Fin.val hk; rw [lookSlots_val] at hv; split_ifs at hv <;> omega
theorem joinSlots_ne (i : Fin 302)
    (h : i.val ≠ 2 ∧ i.val ≠ 6 ∧ i.val ≠ 174 ∧ (i.val < 178 ∨ 211 < i.val) ∧ (i.val < 272 ∨ 298 < i.val)) :
    ∀ k, joinSlots k ≠ i := by
  intro k hk; have hv := congrArg Fin.val hk; rw [joinSlots_val] at hv; split_ifs at hv <;> omega

/-! ## Cost -/

/-- The core's fuel: metadata, arena boot, raw atoms (masked), two moves, lookup, two moves, join. -/
def cost (mcost C w cap poolLen occLen : ℕ) (P lowered : Ring.Poly ℕ) : ℕ :=
  mcost + 1 + (KitBoot.cost C w + 1 + ((2 * CloseoutRowsRawAtomProducer.budget cap poolLen + 2) + 1 +
    ((1 + 1 + (PacketBank.lookupBudget (PolyKit.reserve C w) 0 + 1 + 1)) + 1 +
      MajorityComplete.PacketAtomsJoin.budget C (PolyKit.reserve C w) occLen P lowered)))

end
end NearCubicWires.PacketsConstruction.LowerCore
