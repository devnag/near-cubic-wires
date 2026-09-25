import Proof.CaseAnalysis.RowsFamilyLoop
import Proof.CaseAnalysis.RowsSourceMeaning
import Proof.MachineModel.Run

namespace NearCubicWires.ExtIncidence
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution SupplierPrinter
open RepairOrdinary.CloseoutRowsSourceDigits
open RepairOrdinary.CloseoutRowsCacheInput RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem maskOf_map_val {B : ℕ} (m : List (Fin B)) :
    maskOf B (m.map Fin.val) = List.ofFn (fun i : Fin B => decide (i ∈ m)) := by
  unfold maskOf
  congr 1
  funext i
  apply decide_eq_decide.mpr
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp h
    exact (Fin.ext hji) ▸ hj
  · intro h
    exact List.mem_map.mpr ⟨i, h, rfl⟩

def rawIndices {B : ℕ} (ms : List (List (Fin B))) := ms.map (List.map Fin.val)
def rawRows {B : ℕ} (ms : List (List (Fin B))) :=
  ms.map (fun m=>List.ofFn (fun i : Fin B=>decide (i∈m)))

theorem raw_table_eq_rows {B : ℕ} (ms : List (List (Fin B))) :
    ExtIncidence.table B (rawIndices ms)=(rawRows ms).flatten := by
  simp only [ExtIncidence.table,rawIndices,rawRows,List.map_map,Function.comp_def,
    ExtIncidence.maskOf_map_val]

theorem raw_rows_run {B : ℕ} (ms : List (List (Fin B))) (pre tail out : List Bool) (c : ℕ) :
    ∃ r : ExecutionReceipt 5 7,
      runFrom ExtIncidence.machine (ExtIncidence.cost B (rawIndices ms))
        (ExtIncidence.cfg 0 (pre++ExtIncidence.stream (rawIndices ms)++tail) pre.length B 1
          (List.replicate B false) 0 out c)=some r ∧
      r.final=ExtIncidence.cfg 6 (pre++ExtIncidence.stream (rawIndices ms)++tail)
        (pre.length+(ExtIncidence.stream (rawIndices ms)).length) B 1 (List.replicate B false) 0
        (out++(rawRows ms).flatten) (c+ms.length) ∧
      r.steps=ExtIncidence.cost B (rawIndices ms) := by
  have valid : ∀ m∈rawIndices ms,∀ d∈m,d<B := by
    intro m hm d hd
    obtain ⟨m',_,rfl⟩:=List.mem_map.mp hm
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hd
    exact i.isLt
  obtain ⟨r,hr,hf,hs⟩:=ExtIncidence.stream_run pre tail B (rawIndices ms) valid out c
  refine ⟨r,hr,?_,hs⟩
  rw [raw_table_eq_rows] at hf
  simpa only [rawIndices,List.length_map] using hf

theorem raw_polynomial_value {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    {R C : Type} (holds : Equation l r→R→C→Bool)
    (ms : List (List (Fin gs.length))) (row : R) (column : C) :
    exactPolynomialValue holds (polynomial gs (rawRows ms)) row column=
      exactPolynomialValue (fun i=>holds (coordinates (RowCachedEquation.equation gs[i.val]))) ms row column := by
  unfold exactPolynomialValue polynomialOccurrenceCount
  congr 2
  simp only [polynomial,rawRows,List.map_map,Function.comp_def,CloseoutRowsSourceMeaning.monomial_value]

end NearCubicWires.ExtIncidence
