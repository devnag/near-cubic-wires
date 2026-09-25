import Proof.Packets.PacketsWriterPlanKit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

variable {a : DecompositionAlgorithm}

/-- **(i) Coordinate vectors** for the row's masks, and the mode bit. -/
structure CoordStageK {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) where
  states : ℕ
  machine : Machine (10 + X.w) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  run : ∀ r (k : rcKey a r), k ∈ rcKeys a r → ∀ (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool),
    (∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 → A i = X.layout.bank r (some k) [] i ∧ H i = 0) →
    (∀ i : Fin (10 + X.w), Y.inQ1 i ∨ i.val = 19 ∨ i.val = 20 → A i = List.replicate (X.R r) false ∧ H i = 0) →
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool), Step machine (cost r) H A H' A' ∧
      A' (Y.tape 19 (by omega)) = ZeroPadding.pad (X.R r) (coordWordK K r k) ∧ H' (Y.tape 19 (by omega)) = 0 ∧
      A' (Y.tape 20 (by omega)) = ZeroPadding.pad (X.R r) [modeBit r] ∧ H' (Y.tape 20 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ Y.inQ1 i → i.val ≠ 19 → i.val ≠ 20 → A' i = A i ∧ H' i = H i

/-- **(ii) SYM combine**: shifted one-hot lookups, then the ≤ 4-way normalized conjunction. -/
structure SymCombineStageK {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) where
  states : ℕ
  machine : Machine (10 + X.w) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  run : ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target),
    k ∈ RCFive.RowKeys.symKeys r L target → ∀ (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool),
    (∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 →
      A i = X.layout.bank (.sym r four L target) (some k) [] i ∧ H i = 0) →
    A (Y.tape 19 (by omega)) = ZeroPadding.pad (X.R (.sym r four L target)) (coordWordK K (.sym r four L target) k) →
    H (Y.tape 19 (by omega)) = 0 →
    (∀ i : Fin (10 + X.w), Y.inQ2 i ∨ i.val = 14 →
      A i = List.replicate (X.R (.sym r four L target)) false ∧ H i = 0) →
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool),
      Step machine (cost (.sym r four L target)) H A H' A' ∧
      A' (X.port 14 (by omega)) = ZeroPadding.pad (X.R (.sym r four L target))
        (rowPolyWordK K (.sym r four L target) k) ∧
      H' (X.port 14 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ Y.inQ2 i → i.val ≠ 14 → A' i = A i ∧ H' i = H i

/-- **(iii) THR combine**: the modular radix row over the digit coordinate vectors. -/
structure ThrCombineStageK {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) where
  states : ℕ
  machine : Machine (10 + X.w) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  run : ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
    k ∈ RCFive.RowKeys.thrKeys a r L target → ∀ (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool),
    (∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 →
      A i = X.layout.bank (.thr r four L target) (some k) [] i ∧ H i = 0) →
    A (Y.tape 19 (by omega)) = ZeroPadding.pad (X.R (.thr r four L target)) (coordWordK K (.thr r four L target) k) →
    H (Y.tape 19 (by omega)) = 0 →
    (∀ i : Fin (10 + X.w), Y.inQ3 i ∨ i.val = 14 →
      A i = List.replicate (X.R (.thr r four L target)) false ∧ H i = 0) →
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool),
      Step machine (cost (.thr r four L target)) H A H' A' ∧
      A' (X.port 14 (by omega)) = ZeroPadding.pad (X.R (.thr r four L target))
        (rowPolyWordK K (.thr r four L target) k) ∧
      H' (X.port 14 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ Y.inQ3 i → i.val ≠ 14 → A' i = A i ∧ H' i = H i

/-- The three sub-stages of F1. -/
structure RowPolySplitK {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) where
  coord : CoordStageK Y K
  sym : SymCombineStageK Y K
  thr : ThrCombineStageK Y K

namespace RowPolySplitK
variable {X : WriterShape a} {Y : RowPolyShape X} {K : KitShape a} (s : RowPolySplitK Y K)

def machine :=
  Composition.machine s.coord.machine
    (CloseoutRowsOriginalSwitch.machine s.sym.machine s.thr.machine (Y.tape 20 (by omega)))

def cost (r : Request) : ℕ := s.coord.cost r + 1 + (s.sym.cost r + s.thr.cost r + 2)

theorem pad_head (R : ℕ) (b : Bool) : readTapeBit (ZeroPadding.pad R [b]) 0 = b := by
  simp [readTapeBit, ZeroPadding.pad]

/-- F1's footprint contains the split's handoff tapes and sub-regions. -/
theorem sub_in_P1 (i : Fin (10 + X.w)) (h : Y.inQ1 i ∨ Y.inQ2 i ∨ Y.inQ3 i ∨ i.val = 19 ∨ i.val = 20) :
    X.inP1 i := by
  have hw := Y.hw1
  unfold WriterShape.inP1
  unfold RowPolyShape.inQ1 RowPolyShape.inQ2 RowPolyShape.inQ3 at h
  omega

/-- **The assembly**: (i), then the switch on the mode bit into (ii) or (iii). -/
theorem run (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (H : Fin (10 + X.w) → ℕ)
    (A : Fin (10 + X.w) → List Bool)
    (hkept : ∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 → A i = X.layout.bank r (some k) [] i ∧ H i = 0)
    (hblank : ∀ i : Fin (10 + X.w), X.inP1 i ∨ i.val = 14 → A i = List.replicate (X.R r) false ∧ H i = 0) :
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool), Step s.machine (s.cost r) H A H' A' ∧
      A' (X.port 14 (by omega)) =
        ZeroPadding.pad (X.R r) (rowPolyWordK K r k) ∧
      H' (X.port 14 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ X.inP1 i → i.val ≠ 14 → A' i = A i ∧ H' i = H i := by
  obtain ⟨H1, A1, s1, h19A, h19H, h20A, h20H, f1⟩ := s.coord.run r k hk H A hkept
    (fun i hi => hblank i (Or.inl (sub_in_P1 (Y := Y) i (by
      rcases hi with hi | hi | hi
      · exact Or.inl hi
      · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))))))
  have hbit : readTapeBit (A1 (Y.tape 20 (by omega))) (H1 (Y.tape 20 (by omega))) = modeBit r := by
    rw [h20A, h20H]
    exact pad_head _ _
  have outQ1 : ∀ i : Fin (10 + X.w), ¬ X.inP1 i → ¬ Y.inQ1 i ∧ i.val ≠ 19 ∧ i.val ≠ 20 := by
    intro i hi
    refine ⟨fun h => hi (sub_in_P1 (Y := Y) i (Or.inl h)), fun h => hi (sub_in_P1 (Y := Y) i (by simp [h])),
      fun h => hi (sub_in_P1 (Y := Y) i (by simp [h]))⟩
  have keep1 : ∀ i : Fin (10 + X.w), i.val < 10 → A1 i = A i ∧ H1 i = H i := by
    intro i hi
    have hn : ¬ X.inP1 i := by unfold WriterShape.inP1; omega
    obtain ⟨o1, o2, o3⟩ := outQ1 i hn
    exact f1 i o1 o2 o3
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r four L target =>
    obtain ⟨H2, A2, s2, h14A, h14H, f2⟩ := s.sym.run r four L target k hk H1 A1
      (fun i hi h1 => by rw [(keep1 i hi).1, (keep1 i hi).2]; exact hkept i hi h1) h19A h19H
      (fun i hi => by
        have hq : ¬ Y.inQ1 i ∧ i.val ≠ 19 ∧ i.val ≠ 20 := by
          have hw := Y.hw1
          unfold RowPolyShape.inQ2 at hi
          unfold RowPolyShape.inQ1
          omega
        rw [(f1 i hq.1 hq.2.1 hq.2.2).1, (f1 i hq.1 hq.2.1 hq.2.2).2]
        rcases hi with hi | hi
        · exact hblank i (Or.inl (sub_in_P1 (Y := Y) i (Or.inr (Or.inl hi))))
        · exact hblank i (Or.inr hi))
    have hsw := CloseoutRowsOriginalSwitch.true_run s.sym.machine s.thr.machine (Y.tape 20 (by omega)) s2 hbit
    refine ⟨H2, A2, (s1.seq hsw).enlarge (by unfold cost; omega), h14A, h14H, ?_⟩
    intro i hi h14
    have hq2 : ¬ Y.inQ2 i := fun h => hi (sub_in_P1 (Y := Y) i (Or.inr (Or.inl h)))
    obtain ⟨o1, o2, o3⟩ := outQ1 i hi
    rw [(f2 i hq2 h14).1, (f2 i hq2 h14).2]
    exact f1 i o1 o2 o3
  | thr r four L target =>
    obtain ⟨H2, A2, s2, h14A, h14H, f2⟩ := s.thr.run r four L target k hk H1 A1
      (fun i hi h1 => by rw [(keep1 i hi).1, (keep1 i hi).2]; exact hkept i hi h1) h19A h19H
      (fun i hi => by
        have hq : ¬ Y.inQ1 i ∧ i.val ≠ 19 ∧ i.val ≠ 20 := by
          have hw := Y.hw1
          unfold RowPolyShape.inQ3 at hi
          unfold RowPolyShape.inQ1
          omega
        rw [(f1 i hq.1 hq.2.1 hq.2.2).1, (f1 i hq.1 hq.2.1 hq.2.2).2]
        rcases hi with hi | hi
        · exact hblank i (Or.inl (sub_in_P1 (Y := Y) i (Or.inr (Or.inr (Or.inl hi)))))
        · exact hblank i (Or.inr hi))
    have hsw := CloseoutRowsOriginalSwitch.false_run s.sym.machine s.thr.machine (Y.tape 20 (by omega)) s2 hbit
    refine ⟨H2, A2, (s1.seq hsw).enlarge (by unfold cost; omega), h14A, h14H, ?_⟩
    intro i hi h14
    have hq3 : ¬ Y.inQ3 i := fun h => hi (sub_in_P1 (Y := Y) i (Or.inr (Or.inr (Or.inl h))))
    obtain ⟨o1, o2, o3⟩ := outQ1 i hi
    rw [(f2 i hq3 h14).1, (f2 i hq3 h14).2]
    exact f1 i o1 o2 o3

theorem cost_le' (r : Request) :
    s.cost r ≤ (s.coord.coefficient + s.sym.coefficient + s.thr.coefficient + 3) *
      (r.smallSize a)^(s.coord.degree + s.sym.degree + s.thr.degree) := by
  have hs := RCFive.PacketBounds.positive a r
  set D := s.coord.degree + s.sym.degree + s.thr.degree
  have hmono : ∀ d, d ≤ D → (r.smallSize a)^d ≤ (r.smallSize a)^D := fun d hd => Nat.pow_le_pow_right hs hd
  have h1 := (s.coord.cost_le r).trans (Nat.mul_le_mul_left _ (hmono s.coord.degree (by omega)))
  have h2 := (s.sym.cost_le r).trans (Nat.mul_le_mul_left _ (hmono s.sym.degree (by omega)))
  have h3 := (s.thr.cost_le r).trans (Nat.mul_le_mul_left _ (hmono s.thr.degree (by omega)))
  have hD : 1 ≤ (r.smallSize a)^D := Nat.one_le_pow _ _ hs
  unfold cost
  nlinarith

/-- **F1 from its split.** -/
def stage : RowPolyStageK X K where
  states := _
  machine := s.machine
  cost := s.cost
  coefficient := s.coord.coefficient + s.sym.coefficient + s.thr.coefficient + 3
  degree := s.coord.degree + s.sym.degree + s.thr.degree
  cost_le := s.cost_le'
  run := s.run

end RowPolySplitK

end
end NearCubicWires.PacketsConstruction
