import Proof.SourceAssembly.SLoadMaskReady

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.InputPass
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

variable (w : Nat)

def maskSlots (j : Fin (5 + w)) : Fin (22 + w) :=
  if j.val = 4 then ⟨0, by omega⟩ else ⟨17 + j.val, by omega⟩

theorem maskSlots_injective : Function.Injective (maskSlots w) := by
  intro x y h
  have hv := congrArg Fin.val h
  unfold maskSlots at hv
  apply Fin.ext
  split_ifs at hv <;> simp only at hv <;> omega

def ret (k : Fin 4) : Fin (22 + w) := ⟨11 + k.val, by omega⟩
def retDrv : Fin (22 + w) := ⟨15, by omega⟩
def leadLog : Fin (22 + w) := ⟨16, by omega⟩
def drv : Fin (22 + w) := ⟨1, by omega⟩
def lenSlots (i : Fin 11) : Fin (22 + w) := ⟨i.val, by omega⟩

theorem lenSlots_injective : Function.Injective (lenSlots w) := by
  intro x y h
  have hv := congrArg Fin.val h
  simp only [lenSlots] at hv
  exact Fin.ext hv

def machine (mask : MaskProducer) :=
  Composition.machine
    (SLoad.LeadDriver.machine (retDrv mask.work) (drv mask.work) (ret mask.work)
      (maskSlots mask.work) (leadLog mask.work))
    (Composition.machine (RecoveryFocus.machine (maskSlots mask.work) mask.machine)
      (RecoveryFocus.machine (lenSlots mask.work)
        (AppendOutputLength.machine SLoad.SuffixFrame.raw 7)))

/-- The mask worker's private reserves, extended by `0` beyond its tape count. -/
def blankExt (blank : Fin (5 + w) → Nat) (n : Nat) : Nat := if h : n < 5 + w then blank ⟨n, h⟩ else 0

/-- The entry bank, by tape index (exact level). -/
def entryAt (a : DecompositionAlgorithm) (r : Request) (cap : Nat) (uK um : List Bool)
    (bl : Nat → Nat) : Nat → List Bool
  | 0 => List.replicate (bl 4) false
  | 1 => []
  | 2 => List.replicate cap false
  | 3 => ZeroPadding.pad cap (frame r.nativeWord)
  | 4 => ZeroPadding.pad cap (frame (r.supportWord a))
  | 5 => ZeroPadding.pad cap (frame (r.indexWord a))
  | 6 => ZeroPadding.pad cap (frame (r.topWord a))
  | 7 => []
  | 8 => List.replicate cap false
  | 9 => []
  | 10 => []
  | 11 => ZeroPadding.pad cap (frame (r.supportWord a))
  | 12 => ZeroPadding.pad cap (frame (List.replicate r.q true))
  | 13 => ZeroPadding.pad cap (frame uK)
  | 14 => ZeroPadding.pad cap (frame um)
  | 15 => ZeroPadding.pad cap (frame (List.replicate r.q true))
  | 16 => List.replicate cap false
  | n + 17 => if n < 5 then [] else List.replicate (bl n) false

def entry (a : DecompositionAlgorithm) (r : Request) (cap : Nat) (uK um : List Bool)
    (blank : Fin (5 + w) → Nat) (x : Fin (22 + w)) : List Bool :=
  entryAt a r cap uK um (blankExt w blank) x.val

section entryVals
variable {w : Nat} {a : DecompositionAlgorithm} {r : Request} {cap : Nat} {uK um : List Bool}
  {blank : Fin (5 + w) → Nat}

theorem entry_0 (x : Fin (22 + w)) (h : x.val = 0) :
    entry w a r cap uK um blank x = List.replicate (blank ⟨4, by omega⟩) false := by
  unfold entry; rw [h]; simp only [entryAt, blankExt, dif_pos (show 4 < 5 + w by omega)]
theorem entry_2 (x : Fin (22 + w)) (h : x.val = 2) :
    entry w a r cap uK um blank x = List.replicate cap false := by unfold entry; rw [h]; rfl
theorem entry_3 (x : Fin (22 + w)) (h : x.val = 3) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame r.nativeWord) := by unfold entry; rw [h]; rfl
theorem entry_4 (x : Fin (22 + w)) (h : x.val = 4) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame (r.supportWord a)) := by unfold entry; rw [h]; rfl
theorem entry_5 (x : Fin (22 + w)) (h : x.val = 5) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame (r.indexWord a)) := by unfold entry; rw [h]; rfl
theorem entry_6 (x : Fin (22 + w)) (h : x.val = 6) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame (r.topWord a)) := by unfold entry; rw [h]; rfl
theorem entry_1 (x : Fin (22 + w)) (h : x.val = 1) :
    entry w a r cap uK um blank x = [] := by unfold entry; rw [h]; rfl
theorem entry_7 (x : Fin (22 + w)) (h : x.val = 7) :
    entry w a r cap uK um blank x = [] := by unfold entry; rw [h]; rfl
theorem entry_9 (x : Fin (22 + w)) (h : x.val = 9) :
    entry w a r cap uK um blank x = [] := by unfold entry; rw [h]; rfl
theorem entry_10 (x : Fin (22 + w)) (h : x.val = 10) :
    entry w a r cap uK um blank x = [] := by unfold entry; rw [h]; rfl
theorem entryAt_live (bl : Nat → Nat) (n : Nat) (hn : n < 5) :
    entryAt a r cap uK um bl (n + 17) = [] := by
  simp only [entryAt, if_pos hn]
theorem entryAt_high (bl : Nat → Nat) (n : Nat) (hn : 5 ≤ n) :
    entryAt a r cap uK um bl (n + 17) = List.replicate (bl n) false := by
  simp only [entryAt, if_neg (show ¬ n < 5 by omega)]
theorem entry_live (x : Fin (22 + w)) (h1 : 17 ≤ x.val) (h2 : x.val < 22) :
    entry w a r cap uK um blank x = [] := by
  unfold entry
  have e := entryAt_live (a := a) (r := r) (cap := cap) (uK := uK) (um := um) (blankExt w blank)
    (x.val - 17) (by omega)
  rw [show x.val - 17 + 17 = x.val by omega] at e
  exact e
theorem entry_8 (x : Fin (22 + w)) (h : x.val = 8) :
    entry w a r cap uK um blank x = List.replicate cap false := by unfold entry; rw [h]; rfl
theorem entry_11 (x : Fin (22 + w)) (h : x.val = 11) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame (r.supportWord a)) := by unfold entry; rw [h]; rfl
theorem entry_12 (x : Fin (22 + w)) (h : x.val = 12) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame (List.replicate r.q true)) := by
  unfold entry; rw [h]; rfl
theorem entry_13 (x : Fin (22 + w)) (h : x.val = 13) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame uK) := by unfold entry; rw [h]; rfl
theorem entry_14 (x : Fin (22 + w)) (h : x.val = 14) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame um) := by unfold entry; rw [h]; rfl
theorem entry_15 (x : Fin (22 + w)) (h : x.val = 15) :
    entry w a r cap uK um blank x = ZeroPadding.pad cap (frame (List.replicate r.q true)) := by
  unfold entry; rw [h]; rfl
theorem entry_16 (x : Fin (22 + w)) (h : x.val = 16) :
    entry w a r cap uK um blank x = List.replicate cap false := by unfold entry; rw [h]; rfl
theorem entry_high (x : Fin (22 + w)) (h : 22 ≤ x.val) :
    entry w a r cap uK um blank x = List.replicate (blank ⟨x.val - 17, by omega⟩) false := by
  unfold entry
  have hx := x.isLt
  have e := entryAt_high (a := a) (r := r) (cap := cap) (uK := uK) (um := um) (blankExt w blank)
    (x.val - 17) (by omega)
  rw [show x.val - 17 + 17 = x.val by omega] at e
  rw [e, blankExt, dif_pos (show x.val - 17 < 5 + w by omega)]

end entryVals

theorem aol_left {t : Nat} (a : Fin t → List Bool) (i : Fin t) :
    AppendOutputLength.input a (Fin.castAdd 1 i) = a i := by
  simp only [AppendOutputLength.input, Fin.addCases_left]

theorem aol_right {t : Nat} (a : Fin t → List Bool) :
    AppendOutputLength.input a ((0 : Fin 1).natAdd t) = [] := by
  simp only [AppendOutputLength.input, Fin.addCases_right]

/-- The length run's entry at the nine framing-pass tapes and the two fresh tapes. -/
theorem lenIn (e : Fin 9 → List Bool) (j : Fin 11) :
    AppendOutputLength.input (AppendOutputLength.input e) j
      = if h : j.val < 9 then e ⟨j.val, h⟩ else [] := by
  by_cases h : j.val < 9
  · rw [dif_pos h]
    have key := (aol_left (AppendOutputLength.input e) (Fin.castAdd 1 (⟨j.val, h⟩ : Fin 9))).trans
      (aol_left e ⟨j.val, h⟩)
    have ej : Fin.castAdd 1 (Fin.castAdd 1 (⟨j.val, h⟩ : Fin 9)) = j := Fin.ext rfl
    rw [ej] at key
    exact key
  · rw [dif_neg h]
    by_cases h9 : j.val = 9
    · rw [show j = Fin.castAdd 1 ((0 : Fin 1).natAdd 9) from Fin.ext (by simp [h9]), aol_left, aol_right]
    · rw [show j = (0 : Fin 1).natAdd 10 from Fin.ext (by simp; omega), aol_right]

def cost (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) : Nat :=
  SLoad.LeadDriver.prefixFuel a r + 1 +
    (maskBudget mask.coefficient mask.degree (maskData a r) + 1 +
      (2 * SLoad.RequestFrames.cost r.q r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length + 2))


end
end NearCubicWires.SourceRequest.InputPass
