import Proof.Packets.PacketsXWalkLiteralProducedData

/-! Paid duplication of the width drivers, rank template, and initial coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

theorem raw_run (R : Nat) (A : Fin 433→List Bool)
    (hs : A 71=UnaryTemplate.tape R) (hd : A 99=[]) (hl : A 430=[]) :
    Step rawMachine (2*R+6) (fun _=>0) A (fun _=>0) (rawBank A R) := by
  apply PhysicalFocusBoundary.focus (CycleCommonReserve.of_clock (UWalkUnary.ready false false (R+2) R))
    rawSlots (by decide) (fun _=>0) (fun _=>0) A (rawBank A R)
  · intro i;rfl
  · intro i;fin_cases i <;>simp [UWalkUnary.input,rawSlots,unary_source,hs,hd,hl]
  · intro i;rfl
  · intro i;fin_cases i <;>simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,
      rawBank,rawSlots,unary_source,hs]
  · intro i away
    have h99 : i≠99 := by intro hi;exact away 1 (by simpa [rawSlots] using hi.symm)
    have h430 : i≠430 := by intro hi;exact away 2 (by simpa [rawSlots] using hi.symm)
    exact ⟨rfl,by simp [rawBank,h99,h430]⟩

theorem template_run (R : Nat) (A : Fin 433→List Bool)
    (hs : A 99=List.replicate R true) (hd : A 100=[]) (hl : A 431=[]) :
    Step templateMachine (2*R+8) (fun _=>0) A (fun _=>0) (templateBank A R) := by
  apply PhysicalFocusBoundary.focus (CycleCommonReserve.of_clock (DimensionTemplate.ready false R))
    templateSlots (by decide) (fun _=>0) (fun _=>0) A (templateBank A R)
  · intro i;rfl
  · intro i;fin_cases i <;>simp [DimensionTemplate.input,templateSlots,hs,hd,hl]
  · intro i;rfl
  · intro i;fin_cases i <;>simp [DimensionTemplate.output,templateBank,templateSlots,hs]
  · intro i away
    have h100 : i≠100 := by intro hi;exact away 1 (by simpa [templateSlots] using hi.symm)
    have h431 : i≠431 := by intro hi;exact away 2 (by simpa [templateSlots] using hi.symm)
    exact ⟨rfl,by simp [templateBank,h100,h431]⟩

theorem fanout_run (rank R : Nat) (x y : List Bool) (A : Fin 433→List Bool)
    (hk : rank+2≤R) (hx : x.length≤R) (hy : y.length≤R)
    (hs : A 88=ZeroPadding.pad R (UnaryTemplate.tape rank)) (hxs : A 428=x) (hys : A 429=y)
    (hdr : A 41=List.replicate R true)
    (h105 : A 105=[]) (h95 : A 95=[]) (h96 : A 96=[]) (hl : A 432=[]) :
    Step fanoutMachine (2*R+4) (fun _=>0) A (fun _=>0) (fanoutBank A rank R x y) := by
  have len : ∀i,(fanoutSource rank R x y i).length≤R := by
    intro i;fin_cases i <;>simp [fanoutSource,ZeroPadding.pad_length,UnaryTemplate.tape,hk,hx,hy]
  apply PhysicalFocusBoundary.focus (Step.of_ready (NativeFanout.ready select (fanoutSource rank R x y) R len))
    fanoutSlots (by decide) (fun _=>0) (fun _=>0) A (fanoutBank A rank R x y)
  · intro i;rfl
  · intro i;fin_cases i <;>simp [NativeFanout.input,fanoutSource,fanoutSlots,Fin.addCases,
      hs,hxs,hys,hdr,h105,h95,h96,hl]
  · intro i;rfl
  · intro i;fin_cases i <;>simp [NativeFanout.output,NativeFanout.word,select,fanoutSource,
      fanoutSlots,fanoutBank,Fin.addCases,hs,hxs,hys,hdr,pad_idem]
  · intro i away
    have ha : i≠105 := by intro hi;exact away 3 (by simpa [fanoutSlots] using hi.symm)
    have hb : i≠95 := by intro hi;exact away 4 (by simpa [fanoutSlots] using hi.symm)
    have hc : i≠96 := by intro hi;exact away 5 (by simpa [fanoutSlots] using hi.symm)
    have hd : i≠432 := by intro hi;exact away 7 (by simpa [fanoutSlots] using hi.symm)
    exact ⟨rfl,by simp [fanoutBank,ha,hb,hc,hd]⟩

theorem count_raise_run (A : Fin 433→List Bool) :
    Step countRaise 1 (fun _=>0) A preparedHeads A := by
  apply PhysicalFocusBoundary.focus (PhysicalDriverMoves.run HeadMove.right (fun _ : Fin 1=>0)
    (fun _ : Fin 1=>A 427)) countSlots (by intro i j _;exact Subsingleton.elim i j)
    (fun _=>0) preparedHeads A A
  · intro i;rfl
  · intro i;rfl
  · intro i;simp [countSlots,preparedHeads,HeadMove.apply]
  · intro i;rfl
  · intro i away
    have hi : i≠427 := by intro hi;exact away 0 hi.symm
    exact ⟨by simp [preparedHeads,hi],rfl⟩

end
end Theorem25Completion.WalkLiteralProduced
