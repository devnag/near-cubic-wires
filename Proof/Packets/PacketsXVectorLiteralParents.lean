import Proof.Packets.PacketsXVectorLiteralDeltaGuards
import Proof.Packets.PacketsXVectorWorkerParentsBounded

/-! Both actual arithmetic loops at one descending level, with the concrete
literal delta program. All provider execution and numerical obligations are
proved from the resident layout and frozen global degree census. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource.CloseoutRawRows
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def literalParentInvariant {rank depth population : Nat} (C R : Nat)
    (label : Fin population → BinaryVector rank) (seed : ToeplitzSeed rank) (wins : Fin depth → Nat)
    (level : Fin depth) (baseline : Fin 222 → List Bool) (baselineExtra : Fin 32 → List Bool) (fields : Fin 222 → List Bool)
    (extra : Fin 32 → List Bool) : Prop :=
  LiteralDeltaResident C R (deltaChildCard label seed level) (wins level)
    (deltaLiteralVariableCodes (population:=population) level) fields ∧
  (∀j,j.val<17 → extra j=List.replicate R false) ∧
  (∀j,ProviderRetained j → j≠146 → j≠147 → j≠148 → fields j=baseline j) ∧ extra=baselineExtra

theorem literal_parents_run {rank depth population : Nat} (C w d done : Nat)
    (label : Fin population → BinaryVector rank) (seed : ToeplitzSeed rank) (wins : Fin depth → Nat)
    (hdone : done<depth) (hpop : 1≤population) (hw : 3≤w)
    (hC : (depth+2*population+2)^2≤C)
    (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population*(2*depth+1)+2)^d≤2^w)
    (hW : wins ⟨depth-(done+1),by omega⟩≤64*(C+2))
    (baseline : Fin 222 → List Bool) (baselineExtra : Fin 32 → List Bool) (input : Fin 297 → List Bool)
    (hinput : ParentReady C (commonReserve C w) (depth-(done+1))
      (NormalizedVector.table label seed wins 0 done)
      (levelDelta label seed wins ⟨depth-(done+1),by omega⟩)
      (literalParentInvariant C (commonReserve C w) label seed wins ⟨depth-(done+1),by omega⟩ baseline baselineExtra) 0 input) :
    ∃output,Step (parents WindowProvider.literalProvider)
      (allParentsFuel (commonReserve C w) (literalDeltaFuel C w) (population+1))
      (Fin.addCases (parentH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>ZeroPadding.pad (commonReserve C w) (CompareMachine.word (population+1))))
      (Fin.addCases (parentH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad (commonReserve C w) (CompareMachine.word (population+1)))) ∧
      ParentReady C (commonReserve C w) (depth-(done+1))
        (NormalizedVector.table label seed wins 0 done)
        (levelDelta label seed wins ⟨depth-(done+1),by omega⟩)
        (literalParentInvariant C (commonReserve C w) label seed wins ⟨depth-(done+1),by omega⟩ baseline baselineExtra)
        (population+1) output := by
  let level : Fin depth:=⟨depth-(done+1),by omega⟩
  let ps:=NormalizedVector.table label seed wins 0 done
  let ds:=levelDelta label seed wins level
  let Q:=literalParentInvariant C (commonReserve C w) label seed wins level baseline baselineExtra
  have hlen : ps.length=population+1 := NormalizedVector.table_length label seed wins 0 done
  have splitDegree:=level_degree_split wins done d hdone hdegree
  have deltaDegree : 2*wins level≤d := by dsimp only [level];omega
  obtain ⟨hcodes,hsize,hpositive,hcount,hpopulation⟩:=literal_delta_guards C w d level wins hpop hC deltaDegree hfit
  have reserve : C+2≤commonReserve C w := LiteralCacheReuse.reserve_width C w
  have resident_step : ∀parent child : Fin ps.length,∀next left right fields extra,
      VectorAccumulator.Fits (commonReserve C w) left → VectorAccumulator.Fits (commonReserve C w) right → Q fields extra →
      ∃fields' extra',Step (delta WindowProvider.literalProvider) (literalDeltaFuel C w) (H (fun _=>0))
        (A C (commonReserve C w) child.val parent.val level.val left right
          (masks C (VectorParentPrefix.value ps (ds parent.val) child.val))
          (vectorBank C (commonReserve C w) ps) next fields extra)
        (H (fun _=>0))
        (A C (commonReserve C w) child.val parent.val level.val left (masks C (ds parent.val child.val))
          (masks C (VectorParentPrefix.value ps (ds parent.val) child.val))
          (vectorBank C (commonReserve C w) ps) next fields' extra') ∧ Q fields' extra' := by
    intro parent child next left right fields extra _hl hr hq
    have hp : parent.val<population+1 := by have h:=parent.isLt;omega
    have hc : child.val<population+1 := by have h:=child.isLt;omega
    have hn:=delta_child_card_le label seed level
    obtain ⟨out,run,ready,kept⟩:=literal_delta_resident_run C w (deltaChildCard label seed level)
      (wins level) child.val parent.val level.val (deltaLiteralVariableCodes (population:=population) level)
      (delta_codes_sorted level) hcodes hsize hpositive hw hW hcount (by omega) (by omega) (by omega)
      left right (masks C (VectorParentPrefix.value ps (ds parent.val) child.val))
      (vectorBank C (commonReserve C w) ps) next fields extra hq.1 hr hq.2.1
    have packet : deltaPacket (deltaChildCard label seed level) (wins level) parent.val child.val
        (literalWindowPacket C (deltaLiteralVariableCodes (population:=population) level)
          (deltaChildCard label seed level-wins level) (wins level))=masks C (ds parent.val child.val) := by
      dsimp only [ds]
      rw [levelDelta,dif_pos hp,dif_pos hc]
      exact delta_packet_exact C label seed wins level ⟨parent.val,hp⟩ ⟨child.val,hc⟩
    rw [packet] at run
    refine ⟨out,extra,run,ready,hq.2.1,?_,hq.2.2.2⟩
    intro j hj h146 h147 h148
    exact (kept j hj h146 h147 h148).trans (hq.2.2.1 j hj h146 h147 h148)
  obtain ⟨output,run,ready⟩:=parent_loop_bounded WindowProvider.literalProvider C w d
    (structuralListCoordinateRawDegreeFrom depth wins 0 (depth-done)) (2*wins level) level.val
    (literalDeltaFuel C w) (LiteralAlphabet.codes depth population) ps ds Q input hinput
    (fun j hj=>(LiteralAlphabet.codes_lt_square depth population j hj).trans_le hC)
    (level_table_bounded label seed wins done hdone.le)
    (by
      intro parent hp child hc
      exact level_delta_bounded label seed wins level parent child (by omega) (by omega))
    splitDegree (literal_census depth population d w hfit) (by omega) (by omega) resident_step
  exact ⟨output,by simpa only [hlen] using run,by simpa only [hlen] using ready⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
