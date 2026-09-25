import Proof.Packets.BudgetJ5Loops
import Proof.MachineModel.RuntimeShapeRecipe

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.P1TopDown
open NearCubicWires.RepairOrdinary
open PCJ6e421fabe2aa4155_SourceBundle
namespace NearCubicWires.SourceBudget
noncomputable section

/-- **`sourceConsts`' source degree, explicitly**: no `k` on the right, so `remainingDegree` can be chosen as this
formula before the hierarchy index `kOf … remainingDegree` it determines. -/
theorem sourceConsts_degree (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
    (r dS hT hS m L cP cT cS : ℕ) :
    (sourceConsts sources k p r dS hT hS m L cP cT cS).degree (CloseoutLanguage.selectedPCPP sources) =
      r + (dS + r + reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) +
        5*(r + r) + 2*((r + r) + r) +
        (r + reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources))) := by
  simp only [J5Consts.degree, J5Consts.D, sourceConsts]

/-- The table exponent, explicitly (no `k`): the order constraint is `r + hT + σ + 2 ≤ L`. -/
theorem sourceConsts_tableExp (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
    (r dS hT hS m L cP cT cS : ℕ) :
    (sourceConsts sources k p r dS hT hS m L cP cT cS).tableExp = r + hT := by
  simp only [J5Consts.tableExp, sourceConsts]

/-- **`SplitRuntime` from J5 constants.** If the recipe's `remainingFuel` is `K.fuel` at the worker's own
hierarchy index and its `remainingDegree` is `K.degree`, the split holds with bound `le_refl`, given `2 ≤ m` and
the live scale above the table exponent. -/
theorem splitRuntime_of_consts (d : Choices)
    (K : (sources : EightSources) → (gamma : ℝ) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → J5Consts)
    (hdeg : ∀ sources gamma hg hh p, Choices.remainingDegree d sources gamma hg hh p =
      (K sources gamma hg hh p).degree (CloseoutLanguage.selectedPCPP sources))
    (hfuel : ∀ sources gamma hg hh p n, Choices.remainingFuel d sources gamma hg hh p n =
      (K sources gamma hg hh p).fuel (CloseoutLanguage.selectedPCPP sources) n
        (C10PartsSchedule.widthAt sources
          (SourceParent.kOf (Choices.capIndex d) (Choices.remainingDegree d) sources gamma hg hh p) n))
    (hm : ∀ sources gamma hg hh p, 2 ≤ (K sources gamma hg hh p).m)
    (horder : ∀ sources gamma hg hh p,
      (K sources gamma hg hh p).tableExp + SelectedRuntime.sigma sources + 2 ≤ (K sources gamma hg hh p).L) :
    RuntimeShape.SplitRuntime d := by
  intro sources gamma hg hh p
  refine ⟨{ liveScale := (K sources gamma hg hh p).L
            tableExponent := (K sources gamma hg hh p).tableExp
            smallExponent := (K sources gamma hg hh p).smallExp
            smallDivisor := (K sources gamma hg hh p).m
            sourceCoefficient := (K sources gamma hg hh p).coefP (CloseoutLanguage.selectedPCPP sources)
            tableCoefficient := (K sources gamma hg hh p).coefT
            smallCoefficient := (K sources gamma hg hh p).coefS
            onset := 0
            two_le_divisor := hm sources gamma hg hh p
            order := horder sources gamma hg hh p
            bound := ?_ }⟩
  intro n _
  have e : (n+1)^(Choices.remainingDegree d sources gamma hg hh p) =
      (n+1)^((K sources gamma hg hh p).degree (CloseoutLanguage.selectedPCPP sources)) := by
    rw [hdeg sources gamma hg hh p]
  rw [hfuel sources gamma hg hh p n, e]
  exact le_refl _

end
end NearCubicWires.SourceBudget
end

