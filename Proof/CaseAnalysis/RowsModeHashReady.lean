import Proof.CaseAnalysis.RowsModeLabel

/-! The actual complete hash prefix is prepared for the literal-cache cell
scan. Original seed/label/depth fields are retained; all scan heads return. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReady
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
open CloseoutRowsModeHashLoop CloseoutRowsModeHashSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def final (rank depth C : Nat) (label lower upper translation : List Bool):=
  RepeatMachine.cfg 3 (entry rank C label lower upper translation depth (word rank depth label lower upper translation)) depth 1
def caps (C : Nat) (i : Fin 10):=if i=4 ∨ i=6 ∨ i=8 then C else 0
noncomputable def machine:=MaskedReset.machine CloseoutRowsModeHashSource.machine (fun _=>true)
def budget (rank depth : Nat):=2*(CloseoutRowsModeHashLoop.budget rank depth+2)+2
noncomputable def input (rank depth C : Nat) (label lower upper translation : List Bool) : Fin 11→List Bool:=
  Fin.addCases (m:=10) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps C i) ((source rank depth C label lower upper translation []).tapes i))
    (fun _=>List.replicate C false)
noncomputable def output (rank depth C : Nat) (label lower upper translation : List Bool) : Fin 11→List Bool:=
  Fin.addCases (m:=10) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps C i) ((final rank depth C label lower upper translation).tapes i))
    (fun _=>List.replicate C false)

theorem ready (rank depth C : Nat) (label lower upper translation : List Bool)
    (hd : depth≤rank) (hC : rank+2≤C) (hbudget : CloseoutRowsModeHashLoop.budget rank depth+2≤C) :
    Step machine (budget rank depth) (fun _=>0) (input rank depth C label lower upper translation)
      (fun _=>0) (output rank depth C label lower upper translation):=by
  obtain ⟨r,hr,rf,_⟩:=loop_run rank depth C label lower upper translation [] hd hC
  have raw:=(start_run rank depth C label lower upper translation []).seq
    (Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf))
  have htime:1+1+CloseoutRowsModeHashLoop.budget rank depth=CloseoutRowsModeHashLoop.budget rank depth+2:=by omega
  rw [htime] at raw
  have hstart:∀ i,(source rank depth C label lower upper translation []).heads i=0:=by
    intro i;fin_cases i <;> rfl
  have returned:=(raw.pad (caps C)).mask (fun _=>true) (by intro i hi;exact hstart i) hbudget
  apply (returned.congr_in ?_ rfl).congr ?_ ?_
  · funext i
    refine Fin.addCases (m:=10) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.addCases_left] using hstart j
    · simp only [Fin.addCases_right]
  · funext i;fin_cases i <;> rfl
  · simp only [output,final,List.nil_append]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReady
