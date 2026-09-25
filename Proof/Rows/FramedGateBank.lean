import Proof.Rows.NativeGateLoadReady
import Proof.Rows.UniformMinimumBounds

/-! Fixed original-native traversal bank. Only isolated short gate fields
enter the gate evaluator; the full retained source stays outside its bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FramedGateBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_CellGatePalette
noncomputable section

def strict {q : Nat} (g : NormalizedThresholdGate q) : ExactThresholdGate q :=
 {weight:=g.weight,target:=g.threshold-1}
def coreBank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (fields out : List Bool) : Fin 114→List Bool :=
 Fin.addCases (m:=108) (n:=6) (motive:=fun _=>List Bool)
   (cold (words fields (List.replicate H false) q w (HardwireBudget.C w) R) U out)
   (PCJ45bee56da9f34d5a_MinimumGateCell.extra live x H)
def extras (source framed : List Bool) (H : Nat) : Fin 8→List Bool :=
 ![source,framed,List.replicate H false,List.replicate H false,List.replicate H false,
   List.replicate H false,List.replicate H false,List.replicate H false]
def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (source fields framed out : List Bool) : Fin 122→List Bool :=
 Fin.addCases (m:=114) (n:=8) (motive:=fun _=>List Bool) (coreBank live x w H R U fields out) (extras source framed H)
def extraHeads (pos : Nat) : Fin 8→Nat := ![pos,0,0,0,0,0,0,0]
def heads (pos : Nat) (out : List Bool) : Fin 122→Nat :=
 Fin.addCases (m:=114) (n:=8) (motive:=fun _=>Nat) (PCJ45bee56da9f34d5a_MinimumGateCell.heads out) (extraHeads pos)
def loadSlots : Fin 11→Fin 122 := ![115,116,117,118,119,0,5,120,121,112,113]
def copySlots : Fin 3→Fin 122 := ![114,115,120]
def eraseSlots : Fin 4→Fin 122 := ![0,115,112,113]
theorem loadSlots_injective : Function.Injective loadSlots := by decide
theorem copySlots_injective : Function.Injective copySlots := by decide
theorem eraseSlots_injective : Function.Injective eraseSlots := by decide

theorem bank_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (source fields framed fields' framed' out : List Bool) (i : Fin 122) (h0 : i≠0) (h115 : i≠115) :
 bank live x w H R U source fields framed out i=bank live x w H R U source fields' framed' out i := by
 fin_cases i <;>first | rfl | contradiction

end
end PCJ45bee56da9f34d5a_FramedGateBank
