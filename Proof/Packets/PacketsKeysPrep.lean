import Proof.Packets.PacketsSetup
import Proof.Packets.PacketsWriterPlan
import Proof.Packets.PacketsDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Prep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsConstruction
noncomputable section

variable (a : DecompositionAlgorithm)

theorem relabelN_eq (r : Request) : relabelN a r = childTotal a r := by
  have h1 := alphabet_eq a r
  have h2 : relabelN a r + 2 = Packets.alphabet a (r.family a) := rfl
  have h3 : alphabet a r = Packets.alphabet a (r.family a) := rfl
  omega

theorem relabelY_eq (r : Request) : relabelY a r = twoK a r := rfl

/-- `1^N`. -/
def w0 : WordStage a (fun r => List.replicate (childTotal a r) true) := (childStage a).toWord

/-- `1^(N·2^K + 2)`. -/
def w1 : WordStage a (fun r => List.replicate (childTotal a r * twoK a r + 2) true) :=
  (((childStage a).pairP (twoKStage a) mulMap2 8 2 mul_cost).thenMapP (plusMap 2) (2 * 2 + 4) 1 (plus_cost 2)).toWord

/-- `CompareMachine.word (2^K)`. -/
def w2 : WordStage a (fun r => RepairSource.VerifierDecoding.CompareMachine.word (twoK a r)) :=
  (twoKStage a).thenWordP cmpWordMap 6 1 cmp_cost

/-- The three words, one fixed machine. -/
def vec := (((VecStage.nil a (fun _ _ => [])).snoc (w0 a)).snoc (w1 a)).snoc (w2 a)

/-- The local private-tape count. -/
abbrev e : ℕ := (vec a).extra

/-- The words, then tape 3's head to `1`. -/
def localM := Composition.machine (vec a).machine (PacketsGlue.MoveOne.machine (1 + 3 + e a) ⟨3, by omega⟩)

/-- The local exit. -/
def exitA (r : Request) (i : Fin (1 + 3 + e a)) : List Bool :=
  if i.val = 0 then RepairOrdinary.frame (Request.input a r)
  else if i.val = 1 then List.replicate (childTotal a r) true
  else if i.val = 2 then List.replicate (childTotal a r * twoK a r + 2) true
  else if i.val = 3 then RepairSource.VerifierDecoding.CompareMachine.word (twoK a r)
  else []

theorem local_run (r : Request) :
    ∃ (H' : Fin (1 + 3 + e a) → ℕ) (A' : Fin (1 + 3 + e a) → List Bool),
      Step (localM a) ((vec a).cost r + 1 + 1) (fun _ => 0) (inBank (1 + 3 + e a) (Request.input a r)) H' A' ∧
      ∀ i : Fin (1 + 3 + e a), i.val ≤ 3 → A' i = exitA a r i ∧ H' i = (if i.val = 3 then 1 else 0) := by
  obtain ⟨H1, A1, hs, h0A, h0H, hout⟩ := (vec a).run r
  have hm := PacketsGlue.MoveOne.run (1 + 3 + e a) ⟨3, by omega⟩ H1 A1
  refine ⟨_, _, hs.seq hm, ?_⟩
  intro i hi
  have hA : ∀ j (hj : j < 3), A1 ⟨j + 1, by omega⟩ = (if j = 2 then fun r => RepairSource.VerifierDecoding.CompareMachine.word (twoK a r)
      else (if j = 1 then fun r => List.replicate (childTotal a r * twoK a r + 2) true
        else (if j = 0 then fun r => List.replicate (childTotal a r) true else fun _ => []))) r ∧
      H1 ⟨j + 1, by omega⟩ = 0 := fun j hj => hout j hj
  rcases i with ⟨_ | _ | _ | _ | k, hk⟩
  · refine ⟨?_, ?_⟩
    · simp only [exitA, if_true]; exact h0A
    · simp only [Function.update]
      rw [dif_neg (by simp)]
      exact h0H
  · obtain ⟨a1, h1⟩ := hA 0 (by omega)
    refine ⟨?_, ?_⟩
    · rw [a1]; simp [exitA]
    · simp only [Function.update]
      rw [dif_neg (by simp)]
      simpa using h1
  · obtain ⟨a1, h1⟩ := hA 1 (by omega)
    refine ⟨?_, ?_⟩
    · rw [a1]; simp [exitA]
    · simp only [Function.update]
      rw [dif_neg (by simp)]
      simpa using h1
  · obtain ⟨a1, h1⟩ := hA 2 (by omega)
    refine ⟨?_, ?_⟩
    · rw [a1]; simp [exitA]
    · have h1' : H1 ⟨3, by omega⟩ = 0 := h1
      simp [Function.update, h1']
  · exact absurd hi (by simp only [Fin.val_mk]; omega)

/-! ## Docked into the writer -/

section Dock
variable {a} (X : WriterShape a) (hu : e a ≤ X.w3)

/-- Local `0 ↦ 0`, `1 ↦ 11`, `2 ↦ 16`, `3 ↦ 18`, private `4 + i ↦` the start of `P3`. -/
def slotVal (w1 w2 : ℕ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then 11 else if j = 2 then 16 else if j = 3 then 18 else 19 + w1 + w2 + (j - 4)

def slots (j : Fin (1 + 3 + e a)) : Fin (10 + X.w) :=
  ⟨slotVal X.w1 X.w2 j.val, by
    have := j.isLt; unfold slotVal WriterShape.w; split_ifs <;> omega⟩

theorem slots_val (j : Fin (1 + 3 + e a)) : (slots X hu j).val = slotVal X.w1 X.w2 j.val := rfl

theorem slots_injective : Function.Injective (slots X hu) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [slots_val, slots_val] at hv
  unfold slotVal at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **F3** for the writer shape `X`. -/
def prepStage : RelabelPrepStage X where
  states := _
  machine := RecoveryFocus.machine (slots X hu) (localM a)
  cost := fun r => (vec a).cost r + 1 + 1
  coefficient := (vec a).coefficient + 2
  degree := (vec a).degree
  cost_le := by
    intro r
    have h := (vec a).cost_le r
    have hs : 1 ≤ (r.smallSize a) ^ (vec a).degree := Nat.one_le_pow _ _ (one_le_small a r)
    rw [Nat.add_mul]
    omega
  run := by
    intro r H A h0 hH0 hblank
    obtain ⟨H', A', st, hA'⟩ := local_run a r
    obtain ⟨H'', A'', st', hslot, hother⟩ := Dock.lift st (slots X hu) (slots_injective X hu)
      (fun j => if j.val = 0 then 0 else X.R r) H A (by
        intro j
        by_cases hj : j.val = 0
        · have hs : slots X hu j = X.port 0 (by omega) := Fin.ext (by rw [slots_val]; simp [slotVal, hj, WriterShape.port])
          rw [hs, h0, hH0]
          simp [hj, inBank]
        · have hs : X.inP3 (slots X hu j) ∨ (slots X hu j).val = 11 ∨ (slots X hu j).val = 16 ∨
              (slots X hu j).val = 18 := by
            have hv := slots_val X hu j
            have hjl := j.isLt
            rcases (show j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ 4 ≤ j.val by omega) with h | h | h | h
            · right; left; rw [hv]; simp [slotVal, h]
            · right; right; left; rw [hv]; simp [slotVal, h]
            · right; right; right; rw [hv]; simp [slotVal, h]
            · left
              unfold WriterShape.inP3
              rw [hv]
              unfold slotVal
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
              have he : e a = (vec a).extra := rfl
              constructor <;> omega
          obtain ⟨hA, hH⟩ := hblank _ hs
          refine ⟨hH, ?_⟩
          rw [hA]
          simp only [hj, if_false, inBank]
          rw [Dock.pad_nil_eq])
    have out : ∀ (j : Fin (1 + 3 + e a)), j.val ≤ 3 →
        H'' (slots X hu j) = (if j.val = 3 then 1 else 0) ∧
        A'' (slots X hu j) = ZeroPadding.pad (if j.val = 0 then 0 else X.R r) (exitA a r j) := by
      intro j hj
      obtain ⟨e1, e2⟩ := hslot j
      obtain ⟨f1, f2⟩ := hA' j hj
      rw [e1, e2, f1, f2]
      exact ⟨rfl, rfl⟩
    have p11 := out ⟨1, by omega⟩ (by simp)
    have p16 := out ⟨2, by omega⟩ (by simp)
    have p18 := out ⟨3, by omega⟩ (by simp)
    have s11 : slots X hu ⟨1, by omega⟩ = X.port 11 (by omega) := Fin.ext (by simp [slots_val, slotVal, WriterShape.port])
    have s16 : slots X hu ⟨2, by omega⟩ = X.port 16 (by omega) := Fin.ext (by simp [slots_val, slotVal, WriterShape.port])
    have s18 : slots X hu ⟨3, by omega⟩ = X.port 18 (by omega) := Fin.ext (by simp [slots_val, slotVal, WriterShape.port])
    rw [s11] at p11
    rw [s16] at p16
    rw [s18] at p18
    refine ⟨H'', A'', st', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [p11.2]; simp [exitA, relabelN_eq]
    · rw [p16.2]; simp [exitA, relabelN_eq, relabelY_eq]
    · rw [p18.2]; simp [exitA, relabelY_eq]
    · rw [p11.1]; simp
    · rw [p16.1]; simp
    · rw [p18.1]; simp
    · intro i hi3 h11 h16 h18
      by_cases hin : ∃ j, slots X hu j = i
      · obtain ⟨j, rfl⟩ := hin
        have hj0 : j.val = 0 := by
          by_contra hne
          rw [slots_val] at h11 h16 h18
          unfold WriterShape.inP3 at hi3
          rw [slots_val] at hi3
          unfold slotVal at h11 h16 h18 hi3
          have := j.isLt
          split_ifs at h11 h16 h18 hi3 <;> omega
        have hs : slots X hu j = X.port 0 (by omega) := Fin.ext (by rw [slots_val]; simp [slotVal, hj0, WriterShape.port])
        obtain ⟨o1, o2⟩ := out j (by omega)
        rw [hs] at o1 o2 ⊢
        refine ⟨?_, ?_⟩
        · rw [o2, h0]; simp [hj0, exitA]
        · rw [o1, hH0]; simp [hj0]
      · have hn : ∀ j, slots X hu j ≠ i := fun j hj => hin ⟨j, hj⟩
        obtain ⟨o1, o2⟩ := hother i hn
        exact ⟨o2, o1⟩

end Dock

end
end NearCubicWires.PacketsKeys.Prep


