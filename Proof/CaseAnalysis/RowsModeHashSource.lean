import Proof.CaseAnalysis.RowsModeHashLoop

/-! The complete hash-prefix producer consumes original depth at head zero
and emits the ordered bits of the literal hash of the original seed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashSource
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch RepairSource.VerifierDecoding
open CloseoutRowsModeHashLoop CloseoutRowsModeHashMeaning
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot : Fin 1→Fin 10:=fun _=>9
noncomputable def start:=RecoveryFocus.machine slot (RowCoordinateIncrement.shift .right)
noncomputable def machine:=Composition.machine start CloseoutRowsModeHashLoop.machine
noncomputable def source (rank depth C : Nat) (label lower upper translation out : List Bool):=
  RepeatMachine.cfg 0 (entry rank C label lower upper translation 0 out) depth 0
noncomputable def prepared (rank depth C : Nat) (label lower upper translation out : List Bool):=
  RepeatMachine.cfg 0 (entry rank C label lower upper translation 0 out) depth 1

theorem start_run (rank depth C : Nat) (label lower upper translation out : List Bool) :
    Step start 1 (source rank depth C label lower upper translation out).heads
      (source rank depth C label lower upper translation out).tapes
      (prepared rank depth C label lower upper translation out).heads
      (prepared rank depth C label lower upper translation out).tapes:=by
  obtain ⟨r,hr,rf,_⟩:=RowCoordinateIncrement.shift_run .right 0 (CompareMachine.word depth)
  have raw:=(Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).dock slot (by decide)
    (source rank depth C label lower upper translation out).heads (source rank depth C label lower upper translation out).tapes
    (by intro i;rfl) (by intro i;rfl)
  apply raw.congr
  · funext i
    refine Fin.addCases (m:=9) (n:=1) (fun j=>?_) (fun j=>?_) i
    · rw [dockH_other slot _ _ _ (by intro k h;have hv:=congrArg Fin.val h;change 9=j.val at hv;omega)]
      simp only [source,prepared,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
    · fin_cases j;exact dockH_slot slot (by decide) _ _ 0
  · exact (install_existing slot _ _ (by intro i;rfl)).trans (by
      simp only [source,prepared,RepeatMachine.cfg,controlConfig,TapeEmbedding.config])

theorem word_meaning {rank : Nat} (label : SupplierToeplitzCore.BitVec rank) (seed : SupplierToeplitzCore.ToeplitzSeed rank)
    (depth : Nat) (hd : depth≤rank) :
    word rank depth (bits label) (bits seed.1.1) (bits seed.1.2) (bits seed.2)=
      List.ofFn (fun i : Fin depth=>decide (SupplierToeplitzCore.toeplitzHash label seed ⟨i.val,by omega⟩=1)):=by
  unfold word
  rw [←List.map_eq_flatMap]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map,List.length_range] at hi
    simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn,CloseoutRowsModeHashReturned.value] using
      hash_meaning label seed ⟨i,by omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashSource
