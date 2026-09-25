import Proof.Packets.PacketsCoordInv
import Proof.Packets.PacketsSetup

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual.Donor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

variable {a : DecompositionAlgorithm}

structure Parts (a : DecompositionAlgorithm) (K : KitShape a) where
  cell : CellParts a K
  Rv : Request → ℕ
  Lv : Request → ℕ
  rS : KeyWord a (fun r _ => List.replicate (Rv r) true)
  lS : KeyWord a (fun r _ => List.replicate (Lv r) true)
  mS : KeyWord a (fun r _ => [modeBit r])
  cS : KeyWord a (fun r k => CompareMachine.word (maskCount a r k))

namespace Parts
variable {K : KitShape a} (D : Parts a K)

/-- End of the cell scratch region; private bases. -/
def S : ℕ := D.cell.Tc + 5
def p1 : ℕ := D.S + D.rS.extra
def p2 : ℕ := D.p1 + D.lS.extra
def p3 : ℕ := D.p2 + D.mS.extra

def extra : ℕ := D.cell.Tc - 6 + D.rS.extra + D.lS.extra + D.mS.extra + D.cS.extra
def T : ℕ := 11 + D.extra

theorem sizes : 17 ≤ D.S ∧ D.S ≤ D.p1 ∧ D.p1 ≤ D.p2 ∧ D.p2 ≤ D.p3 ∧ D.p3 + D.cS.extra = D.T ∧
    D.S + D.rS.extra = D.p1 ∧ D.p1 + D.lS.extra = D.p2 ∧ D.p2 + D.mS.extra = D.p3 := by
  have := D.cell.Tc_ge
  unfold T extra p3 p2 p1 S
  omega

theorem T_ge : 760 ≤ D.T := by have := D.cell.Tc_ge; unfold T extra; omega

def m1 := RecoveryFocus.machine (kwSlot D.T 14 D.S D.rS.extra (by have := D.T_ge; omega)
  (by have := D.sizes; omega) (by have := D.T_ge; omega)) D.rS.machine
def m2 := RecoveryFocus.machine (kwSlot D.T 12 D.p1 D.lS.extra (by have := D.T_ge; omega)
  (by have := D.sizes; omega) (by have := D.T_ge; omega)) D.lS.machine
def m3 := RecoveryFocus.machine (kwSlot D.T 10 D.p2 D.mS.extra (by have := D.T_ge; omega)
  (by have := D.sizes; omega) (by have := D.T_ge; omega)) D.mS.machine
def m4 := RecoveryFocus.machine (kwSlot D.T 15 D.p3 D.cS.extra (by have := D.T_ge; omega)
  (by have := D.sizes; omega) (by have := D.T_ge; omega)) D.cS.machine
/-- The counter tape. -/
def cnt : Fin D.T := ⟨15, by have := D.T_ge; omega⟩
def m5 := PacketsGlue.MoveOne.machine D.T D.cnt

/-- **The pre-phase machine.** -/
def preMachine := Composition.machine (Composition.machine (Composition.machine (Composition.machine D.m1 D.m2)
  D.m3) D.m4) D.m5

def preCost (r : Request) : ℕ := D.rS.cost r + 1 + D.lS.cost r + 1 + D.mS.cost r + 1 + D.cS.cost r + 1 + 1

/-- The written-port sets, stage by stage. -/
def W1 : ℕ → Bool := fun u => (fun _ => false) u || u == 14
def W2 : ℕ → Bool := fun u => W1 u || u == 12
def W3 : ℕ → Bool := fun u => W2 u || u == 10
def W4 : ℕ → Bool := fun u => W3 u || u == 15

end Parts

/-- The four written ports' final words. -/
theorem portWord_W4 (mode : Bool) (L R Llog cap M : ℕ) :
    portWord Parts.W4 mode L R Llog cap M 10 = [mode] ∧ portWord Parts.W4 mode L R Llog cap M 12 = List.replicate L true ∧
    portWord Parts.W4 mode L R Llog cap M 14 = List.replicate R true ∧
    portWord Parts.W4 mode L R Llog cap M 15 = CompareMachine.word M := by
  simp [portWord, Parts.W4, Parts.W3, Parts.W2, Parts.W1]

/-- **The pre-phase run.** From the exact entry, the four ports written, every private region dirty, the counter
head at 1. -/
theorem pre_run {K : KitShape a} (D : Parts a K) (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r)
    (Llog cap : ℕ) :
    ∃ (H : Fin D.T → ℕ) (A : Fin D.T → List Bool),
      Step D.preMachine (D.preCost r) (fun _ => 0)
        (dEntry a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k))
        (Function.update H D.cnt 1) A ∧
      DInv a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) Parts.W4 D.T H A := by
  have hsz := D.sizes
  have h0 := dInv_init a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) hsz.1
  refine (dkw_step a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) D.rS hk 14 D.S
    (by omega) (le_refl _) hsz.1 (by omega) (fun _ => false) rfl
    (by simp [portWord]) _ _ h0).elim fun H1 e1 => e1.elim fun A1 f1 => ?_
  have s1 := f1.1
  have i1 := f1.2
  rw [hsz.2.2.2.2.2.1] at i1
  refine (dkw_step a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) D.lS hk 12 D.p1
    (by omega) (by omega) hsz.1 (by omega) Parts.W1 (by simp [Parts.W1])
    (by simp [portWord]) _ _ i1).elim fun H2 e2 => e2.elim fun A2 f2 => ?_
  have s2 := f2.1
  have i2 := f2.2
  rw [hsz.2.2.2.2.2.2.1] at i2
  refine (dkw_step a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) D.mS hk 10 D.p2
    (by omega) (by omega) hsz.1 (by omega) Parts.W2 (by simp [Parts.W2, Parts.W1])
    (by simp [portWord]) _ _ i2).elim fun H3 e3 => e3.elim fun A3 f3 => ?_
  have s3 := f3.1
  have i3 := f3.2
  rw [hsz.2.2.2.2.2.2.2] at i3
  refine (dkw_step a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) D.cS hk 15 D.p3
    (by omega) (by omega) hsz.1 (by omega) Parts.W3 (by simp [Parts.W3, Parts.W2, Parts.W1])
    (by simp [portWord]) _ _ i3).elim fun H4 e4 => e4.elim fun A4 f4 => ?_
  have s4 := f4.1
  have i4 := f4.2
  rw [hsz.2.2.2.2.1] at i4
  have h15 : H4 D.cnt = 0 := (i4.port D.cnt (by unfold Parts.cnt; simp) (by unfold Parts.cnt; simp)).2
  have s5 := PacketsGlue.MoveOne.run D.T D.cnt H4 A4
  rw [h15, Nat.zero_add] at s5
  exact ⟨H4, A4, Step.seq (Step.seq (Step.seq (Step.seq s1 s2) s3) s4) s5, i4⟩

end
end NearCubicWires.PacketsConstruction.Residual.Donor
