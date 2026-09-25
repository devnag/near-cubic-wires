import Proof.CaseAnalysis.WitnessFamilyResourcesFits
import Proof.Circuits.PaddedRunnerBudgetClosure

/-! Coarse costs of the actual term, sum and outer-family loops, including
their already-checked loads, mask returns, clears and reinitialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def termCost (S P : ℕ) := 10000*(S+2)*(P+1)
def sumCost (S P : ℕ) := 1000*(S+2)*(termCost S P+P+1)
def totalCost (S P : ℕ) := 100*(S+2)*(sumCost S P+P+1)

theorem total_cost (S P V C T k : ℕ) (bits arity : List Bool)
    (hf : Fits P V C T k bits arity) (hv : V ≤ S) :
    FamilyCold.budget P (P+1) V (sumCost S P) bits ≤ totalCost S P := by
  have hh:=hf.header
  have hm:=Nat.mul_le_mul_right (sumCost S P+3) hv
  unfold FamilyCold.budget FamilyPrepare.budget FamilyRun.budget FamilyWork.budget totalCost
  nlinarith

theorem costs_polynomial {S P : ℕ→ℕ} (hs : SourcePoly S) (hp : SourcePoly P) :
    SourcePoly (fun n=>termCost (S n) (P n)) ∧
      SourcePoly (fun n=>sumCost (S n) (P n)) ∧
      SourcePoly (fun n=>totalCost (S n) (P n)) := by
  have hc (v : ℕ) : SourcePoly (fun _=>v) := polyDominated_const v
  have ht:=((hs.add (hc 2)).const_mul 10000).mul (hp.add (hc 1))
  have hu:=((hs.add (hc 2)).const_mul 1000).mul ((ht.add hp).add (hc 1))
  exact ⟨ht,hu,((hs.add (hc 2)).const_mul 100).mul ((hu.add hp).add (hc 1))⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
