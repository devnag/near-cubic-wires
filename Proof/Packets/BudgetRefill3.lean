import Proof.SourceAssembly.SourceRefillSeam3
import Proof.Packets.BudgetSeamWindows
import Proof.Packets.BudgetCycFuel

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

theorem refreshCost_eq (Rc : ℕ) : Rest.refreshCost Rc = 14*Rc + 34 := by
  unfold Rest.refreshCost; omega

section seam
variable (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
  {printer : WilliamsAlgorithm} (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
  (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
  (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
  (caps : RowCaps) (M2 U0 S Rw B v : Nat)
  {vE vP : Request → Nat} (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
  (g7cost : Nat → Nat) (rq : Request) (Rc w q L Mb Ms j : Nat)

/-- **`hcost`'s left side at `Rk = 16(Rc+1)` is `96·Rc` plus the `Rc`-free part.** -/
theorem refill3_fuel_eq :
    Rest.cycFuel mask packet rows r layout facts caps M2 U0 S Rw B v
        ((4*(16*(Rc+1))+7) + 1 + ((4*Rc+7) + 1 + (Rest.restCost se sp g7cost rq Rc w q L Mb Ms j + 1 +
          Rest.refreshCost Rc))) =
      96*Rc + (Rest.restCost se sp g7cost rq 0 w q L Mb Ms j +
        Rest.cycFuel mask packet rows r layout facts caps M2 U0 S Rw B v 0 + 115) := by
  rw [cycFuel_add, Rest.restCost_eq, refreshCost_eq]
  omega

end seam

/-- **`windows_of_free`'s premise is satisfiable** (class form): if `restCost|₀ + cycFuel 0` lies in class `y` at
`q = widthAt sources k n`, then `restCost|₀ + cycFuel 0 + 2 ≤ Rc = C·tableClass L hR q` past an onset chosen after `L`, for every
`C ≥ 1`, once `hR ≥ y.hT + 2` and `y.dP + 1 ≤ k + 2`. With S's `windows_of_free` this gives `hwinI` and `hwinZ` at `Rk = 16(Rc+1)`. -/
theorem windows3_sat (sources : EightSources) (k : ℕ) (y : CostCls) (m L : ℕ) (hm : 2 ≤ m) (hk : y.dP + 1 ≤ k + 2) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ free : ℕ, y.In m L n (C10PartsSchedule.widthAt sources k n) free →
      ∀ C hR : ℕ, 1 ≤ C → y.hT + 2 ≤ hR →
        free + 2 ≤ C * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n0, h0⟩ := class_fuel_lt_Rc sources k y m L 0 1 hm hk
  refine ⟨n0, fun n hn free hf C hR hC hTR => ?_⟩
  have h1 : 1 ≤ 1 * tableClass L 0 (C10PartsSchedule.widthAt sources k n) := by
    rw [one_mul]; exact SourceConstruction.one_le_tableClass _ _ _
  have h := h0 n hn free 1 hf h1 C hR hC hTR (by omega)
  omega

end
end NearCubicWires.SourceBudget
end

