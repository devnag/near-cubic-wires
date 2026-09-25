import Proof.SourceAssembly.SourceBundle

/- Read the actual queried literal pair, retaining its clause cursor and native cache.
The extra parser templates remain explicit paid-preprocessing inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceLiteralRefs
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
open CloseoutRowsOriginalClause
noncomputable section

def extra (C : Nat) : Fin 72→List Bool :=
  Fin.addCases (m:=27) (n:=45) (CloseoutRowsOriginalClause.extra C) (CloseoutRowsOriginalClassify.extra C)
def bank (C : Nat) (cache : Fin 19→List Bool) : Fin 91→List Bool := Fin.addCases (m:=19) (n:=72) (motive:=fun _=>List Bool) cache (extra C)
theorem bank_eq (C : Nat) (cache : Fin 19→List Bool) : bank C cache=
    CloseoutRowsOriginalClassify.data C (CloseoutRowsOriginalClause.data C cache) := by
  funext i;fin_cases i <;>rfl

def heads := CloseoutRowsOriginalClassify.heads
def bump := DecompositionCountPosition.move (fun i : Fin 91=>if i=13 ∨ i=14 then .right else .stay)
def sourceCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) :=
  let p:=(a.output r).clauses ci
  PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+
    CloseoutRowsOriginalPair.cleanBudget (index p.left) (index p.right) C (negative p.left) (negative p.right)+1+
    (CloseoutCaseTwo.Metadata.budget r (a.output r)+1+
      CloseoutCaseTwo.VariablePrep.budget (index p.left) (a.output r).systematicBits+1+
      CloseoutCaseTwo.VariablePrep.budget (index p.right) (a.output r).systematicBits)

theorem bump_run (A : Fin 91→List Bool) : Step bump 1 (fun _=>0) A heads A := by
  obtain ⟨s,hs,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 91=>if i=13 ∨ i=14 then .right else .stay) (fun _=>0) A
  apply Step.of_run hs
  · rw [hf];funext i;fin_cases i <;>rfl
  · rw [hf]

end
end PCJ6e421fabe2aa4155_SourceLiteralRefs
