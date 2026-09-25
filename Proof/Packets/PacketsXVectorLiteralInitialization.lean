import Proof.Packets.PacketsXVectorLiteralState
import Proof.Packets.PacketsXVectorLiteralCompleteLoop

/-! Physical initialization supplies the exact level-loop entry invariant. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section
attribute [local irreducible] VectorNumericArena.initializeController

theorem cold_data_extra (C R : Nat) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool) (j : Fin 32) :
    coldData C R fields extra ((j.natAdd 264).castAdd 3)=extra j := by
  change coldData C R fields extra (((j.natAdd 264).castAdd 2).castAdd 1)=_
  simp only [coldData,A,Fin.addCases_left,Fin.addCases_right]

theorem initialized_heads : VectorNumericArena.heads=
    Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1) := by decide

theorem initialize_cold_run (C R M root depth : Nat) (p : Parameters)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralColdState C R M root depth p fields extra)
    (hC : C≤R) (hR : 2≤R) (hd : depth+1≤R)
    (hcap : Completion.SourceDigitWidth.capacity (2*M)≤R) :
    Step VectorNumericArena.initializeController (VectorNumericArena.initializeBudget R C M)
      (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1)) (coldData C R fields extra)
      (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1)) (bootData C R M depth fields extra) := by
  have run:=VectorNumericArena.initialize_controller_run R C M depth (coldData C R fields extra) hC hR hd hcap
    rfl rfl rfl rfl h.sourceDepth h.sourcePopulation rfl rfl
    (by
      intro i hi
      simp only [VectorNumericArena.blankPorts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first
        | exact h.blankMode
        | exact h.blankDigit
        | exact h.cold 17 (by decide)
        | exact h.cold 18 (by decide)
        | rfl
        | exact GradedWindow.zero_count R (by omega))
    (by
      intro j
      have hj : VectorNumericArena.widthSlots j=
          ((⟨19+j.val,by omega⟩ : Fin 32).natAdd 264).castAdd 3 := by apply Fin.ext;dsimp [VectorNumericArena.widthSlots];omega
      rw [hj,cold_data_extra]
      exact h.cold _ (by dsimp;omega))
  rw [initialized_cold_data C R M depth fields extra (by omega),initialized_heads] at run
  exact run

theorem initialized_level_ready (C R M root depth rank : Nat) (p : Parameters)
    (label : Fin M → BinaryVector rank) (seed : ToeplitzSeed rank) (wins : Fin depth → Nat)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralColdState C R M root depth p fields extra) (hC : C≤R) (hR : 2≤R) :
    LevelReady C R (M+1) depth (NormalizedVector.table label seed wins 0)
      (literalLoopState C R M root depth p (List.replicate C [])) 0
      (levelData C R (M+1) 0 0 depth [List.replicate C false] []
        (PacketVector.bank R ([List.replicate C false]::List.replicate M []))
        (PacketVector.bank R (List.replicate (M+1) [])) (bootFields R M fields) (bootExtra R M extra)) := by
  refine ⟨0,0,[List.replicate C false],[],bootFields R M fields,bootExtra R M extra,
    by omega,by omega,?_,?_⟩
  · refine ⟨?_,?_,cold_state_boot C R M root depth p fields extra h (by omega)⟩
    · simp only [VectorAccumulator.Fits,List.flatten_cons,List.flatten_nil,List.append_nil,
        List.length_replicate,List.length_cons,List.length_nil]
      exact ⟨hC,hR⟩
    · simp [VectorAccumulator.Fits];omega
  · simp only [Nat.sub_zero,vectorBank,NormalizedVector.table,NormalizedVector.terminal]
    rw [show masks C=List.map (maskNat C) from rfl,VectorTerminal.terminal_masks]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
