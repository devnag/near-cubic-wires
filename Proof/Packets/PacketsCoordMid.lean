import Proof.Packets.PacketsCoordPrep

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

variable {a : DecompositionAlgorithm}

/-- **The mask cell's middle holes.** -/
structure MidParts (a : DecompositionAlgorithm) (K : KitShape a) where
  bS : KeyWord a (fun r _ => List.replicate (Bof a r) true)
  popS : KeyWord a (fun r _ => List.replicate (popOf a r) true)
  cS : KeyWord a (fun r _ => List.replicate (K.C r) true)
  rootS : KeyWord a (fun r _ => List.replicate (rootOf a r) true)
  maskS : KeyStage a (fun r k j => (maskBitsList a r k).getD j [])
  labelsS : KeyWord a (labelsOf a)
  nS : KeyWord a (fun r _ => CompareMachine.word (nOf a r))
  xS : KeyWord a (startXOf a)
  yS : KeyWord a (startYOf a)
  wS : KeyWord a (fun r _ => List.replicate (K.w r) true)
  termS : KeyWord a (fun r _ => PolyKit.vector (K.C r) (K.w r) (ConeDegenerate.terminalVec (popOf a r)))

namespace MidParts
variable {K : KitShape a} (P : MidParts a K)

/-! ## Private bases and the bank size -/

def b1 : ℕ := 752 + P.bS.extra
def b2 : ℕ := P.b1 + P.popS.extra
def b3 : ℕ := P.b2 + P.cS.extra
def b4 : ℕ := P.b3 + P.rootS.extra
def b5 : ℕ := P.b4 + P.maskS.extra
def b6 : ℕ := P.b5 + P.labelsS.extra
def b7 : ℕ := P.b6 + P.nS.extra
def b8 : ℕ := P.b7 + P.xS.extra
def b9 : ℕ := P.b8 + P.yS.extra
def b10 : ℕ := P.b9 + P.wS.extra
/-- The middle bank's size. -/
def Tm : ℕ := P.b10 + P.termS.extra

theorem bases : 752 ≤ P.b1 ∧ P.b1 ≤ P.b2 ∧ P.b2 ≤ P.b3 ∧ P.b3 ≤ P.b4 ∧ P.b4 ≤ P.b5 ∧ P.b5 ≤ P.b6 ∧
    P.b6 ≤ P.b7 ∧ P.b7 ≤ P.b8 ∧ P.b8 ≤ P.b9 ∧ P.b9 ≤ P.b10 ∧ P.b10 ≤ P.Tm := by
  unfold Tm b10 b9 b8 b7 b6 b5 b4 b3 b2 b1; omega

theorem Tm_ge : 752 ≤ P.Tm := by have := P.bases; omega

/-! ## The machines -/

def m1 := RecoveryFocus.machine (kwSlot P.Tm 10 752 P.bS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b1 at this; omega) (by have := P.Tm_ge; omega)) P.bS.machine
def m2 := RecoveryFocus.machine (kwSlot P.Tm 21 P.b1 P.popS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b2 at this; omega) (by have := P.Tm_ge; omega)) P.popS.machine
def m3 := RecoveryFocus.machine (kwSlot P.Tm 50 P.b2 P.cS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b3 at this; omega) (by have := P.Tm_ge; omega)) P.cS.machine
def m4 := RecoveryFocus.machine (kwSlot P.Tm 52 P.b3 P.rootS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b4 at this; omega) (by have := P.Tm_ge; omega)) P.rootS.machine
def m5 := RecoveryFocus.machine (ksSlot P.Tm 56 P.b4 P.maskS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b5 at this; omega) (by have := P.Tm_ge; omega)) P.maskS.machine
def m6 := RecoveryFocus.machine (kwSlot P.Tm 112 P.b5 P.labelsS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b6 at this; omega) (by have := P.Tm_ge; omega)) P.labelsS.machine
def m7 := RecoveryFocus.machine (kwSlot P.Tm 437 P.b6 P.nS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b7 at this; omega) (by have := P.Tm_ge; omega)) P.nS.machine
def m8 := RecoveryFocus.machine (kwSlot P.Tm 438 P.b7 P.xS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b8 at this; omega) (by have := P.Tm_ge; omega)) P.xS.machine
def m9 := RecoveryFocus.machine (kwSlot P.Tm 439 P.b8 P.yS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b9 at this; omega) (by have := P.Tm_ge; omega)) P.yS.machine
def m10 := RecoveryFocus.machine (kwSlot P.Tm 443 P.b9 P.wS.extra (by have := P.Tm_ge; omega)
  (by have := P.bases; unfold b10 at this; omega) (by have := P.Tm_ge; omega)) P.wS.machine

/-- The preparation: ten docked stages in order. -/
def prepMachine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (Composition.machine P.m1 P.m2) P.m3) P.m4)
      P.m5) P.m6) P.m7) P.m8) P.m9) P.m10

def prepCost (r : Request) : ℕ :=
  P.bS.cost r + 1 + P.popS.cost r + 1 + P.cS.cost r + 1 + P.rootS.cost r + 1 + P.maskS.cost r + 1 +
    P.labelsS.cost r + 1 + P.nS.cost r + 1 + P.xS.cost r + 1 + P.yS.cost r + 1 + P.wS.cost r

/-- The external machine docked on the region (`v ↦ 10 + v`). -/
def allSlot (i : Fin 742) : Fin P.Tm := ⟨10 + i.val, by have := P.Tm_ge; have := i.isLt; omega⟩

theorem allSlot_injective : Function.Injective P.allSlot := by
  intro x y h
  have hv := congrArg Fin.val h
  simp only [allSlot] at hv
  exact Fin.ext (by omega)

def allM := RecoveryFocus.machine P.allSlot Theorem25Completion.WalkLiteralProducedMajority.machine
def termM := RecoveryFocus.machine (kwSlot P.Tm 714 P.b10 P.termS.extra (by have := P.Tm_ge; omega)
  (by unfold Tm; omega) (by have := P.Tm_ge; omega)) P.termS.machine

/-- The unary `B` tape (region tape 0). -/
def bTape : Fin P.Tm := ⟨10, by have := P.Tm_ge; omega⟩

/-- **The middle machine**: preparation, then the `B` switch. -/
def midMachine := Composition.machine P.prepMachine
  (CloseoutRowsOriginalSwitch.machine P.allM P.termM P.bTape)

def midCost (r : Request) (k : rcKey a r) (j : ℕ) : ℕ :=
  P.prepCost r + 1 + (ConeRun.budgetOf a K r k j + P.termS.cost r + 2)

end MidParts

/-! ## The runs -/

section Runs
variable {K : KitShape a} (P : MidParts a K)

/-- The written slots after preparation. -/
def slotSet (v : ℕ) : Prop :=
  v = 0 ∨ v = 11 ∨ v = 40 ∨ v = 42 ∨ v = 46 ∨ v = 102 ∨ v = 427 ∨ v = 428 ∨ v = 429 ∨ v = 433

theorem allTable_other (C w root pop B n : ℕ) (mask x y code : List Bool) (v : ℕ) (hv : ¬ slotSet v) :
    allTable C w root pop B n mask x y code v = [] := by
  unfold slotSet at hv
  simp only [not_or] at hv
  obtain ⟨h0, h11, h40, h42, h46, h102, h427, h428, h429, h433⟩ := hv
  simp only [allTable, h0, h11, h40, h42, h46, h102, h427, h428, h429, h433, if_false]

/-- **Preparation**: from `keyEntry`, the ten words on their region slots. -/
theorem prep_run (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) :
    ∃ (H : Fin P.Tm → ℕ) (A : Fin P.Tm → List Bool),
      Step P.prepMachine (P.prepCost r) (fun _ => 0) (keyEntry a r k j P.Tm) H A ∧
      (∀ i : Fin P.Tm, i.val < 10 → A i = keyEntry a r k j P.Tm i ∧ H i = 0) ∧
      (∀ i : Fin P.Tm, 10 ≤ i.val → i.val < 752 →
        A i = allTable (K.C r) (K.w r) (rootOf a r) (popOf a r) (Bof a r) (nOf a r) ((maskBitsList a r k).getD j [])
          (startXOf a r k) (startYOf a r k) (labelsOf a r k) (i.val - 10) ∧ H i = 0) ∧
      (∀ i : Fin P.Tm, P.b10 ≤ i.val → A i = [] ∧ H i = 0) := by
  have hb := P.bases
  have I0 := midInv_init a K r k j P.Tm
  obtain ⟨H1, A1, s1, I1⟩ := kw_step a K r k j P.bS hk P.Tm 10 752 (by omega) (by omega) le_rfl
    (by unfold MidParts.b1 at hb; omega) _ rfl rfl _ _ I0
  obtain ⟨H2, A2, s2, I2⟩ := kw_step a K r k j P.popS hk P.Tm 21 P.b1 (by omega) (by omega) (by omega)
    (by unfold MidParts.b2 at hb; omega) _ rfl rfl _ _ I1
  obtain ⟨H3, A3, s3, I3⟩ := kw_step a K r k j P.cS hk P.Tm 50 P.b2 (by omega) (by omega) (by omega)
    (by unfold MidParts.b3 at hb; omega) _ rfl rfl _ _ I2
  obtain ⟨H4, A4, s4, I4⟩ := kw_step a K r k j P.rootS hk P.Tm 52 P.b3 (by omega) (by omega) (by omega)
    (by unfold MidParts.b4 at hb; omega) _ rfl rfl _ _ I3
  obtain ⟨H5, A5, s5, I5⟩ := ks_step a K r k j P.maskS hk hj P.Tm 56 P.b4 (by omega) (by omega) (by omega)
    (by unfold MidParts.b5 at hb; omega) _ rfl rfl _ _ I4
  obtain ⟨H6, A6, s6, I6⟩ := kw_step a K r k j P.labelsS hk P.Tm 112 P.b5 (by omega) (by omega) (by omega)
    (by unfold MidParts.b6 at hb; omega) _ rfl rfl _ _ I5
  obtain ⟨H7, A7, s7, I7⟩ := kw_step a K r k j P.nS hk P.Tm 437 P.b6 (by omega) (by omega) (by omega)
    (by unfold MidParts.b7 at hb; omega) _ rfl rfl _ _ I6
  obtain ⟨H8, A8, s8, I8⟩ := kw_step a K r k j P.xS hk P.Tm 438 P.b7 (by omega) (by omega) (by omega)
    (by unfold MidParts.b8 at hb; omega) _ rfl rfl _ _ I7
  obtain ⟨H9, A9, s9, I9⟩ := kw_step a K r k j P.yS hk P.Tm 439 P.b8 (by omega) (by omega) (by omega)
    (by unfold MidParts.b9 at hb; omega) _ rfl rfl _ _ I8
  obtain ⟨H10, A10, s10, I10⟩ := kw_step a K r k j P.wS hk P.Tm 443 P.b9 (by omega) (by omega) (by omega)
    (by unfold MidParts.b10 at hb; omega) _ rfl rfl _ _ I9
  refine ⟨H10, A10, (((((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8).seq s9).seq s10), I10.key,
    ?_, I10.fresh⟩
  intro i h10 h752
  refine ⟨?_, (I10.region i h10 h752).2⟩
  rw [(I10.region i h10 h752).1]
  simp only [regionWord]
  split_ifs with hw
  · rfl
  · rw [allTable_other]
    intro hs
    apply hw
    unfold slotSet at hs
    rcases hs with h | h | h | h | h | h | h | h | h | h <;> simp [h]

end Runs

end
end NearCubicWires.PacketsConstruction.Residual
