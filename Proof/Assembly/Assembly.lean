import Proof.Assembly.Front

/-! The checked physical join: initialize the resident descriptor bank,
preserve the denominator outside the focus, and retain the exact fuel sum. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ2bf639ce0c7c470f_Assembly
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit

attribute [local irreducible] CompetitorCrossScheduler.producer
  P1TopDownPaidReusable.machine P1TopDownPaidReloadCore.rawMachine
  P1TopDownPaidReusableBody.machine


noncomputable def familyLocal (a : WilliamsAlgorithm) (j : Fin (r_tapes a)) :
    Fin (initTapes a) := by
  unfold initTapes
  exact j.castAdd 7

theorem input_heads_independent (a : WilliamsAlgorithm)
    (ds : List P1TopDownPaidReusable.Datum) (S R B N : Nat) :
    r_inputH a [] 0 0 0 0 = r_inputH a ds S R B N := by
  funext j
  simp only [r_inputH, f_entry, RepeatMachine.cfg, controlConfig,
    TapeEmbedding.config, P1TopDownPaidReusable.source, List.take_zero,
    List.flatMap_nil, List.length_nil]

theorem exit_heads_family (a : WilliamsAlgorithm)
    (ds : List P1TopDownPaidReusable.Datum) (S R B N : Nat) (j : Fin (r_tapes a)) :
    exitH a (familyLocal a j) = r_inputH a ds S R B N j := by
  change Fin.addCases (motive := fun _ => Nat) (r_inputH a [] 0 0 0 0) (fun _ : Fin 7 => 1)
    (j.castAdd 7) = _
  rw [Fin.addCases_left, input_heads_independent a ds S R B N]

theorem family_bank_input (a : WilliamsAlgorithm)
    (ds : List P1TopDownPaidReusable.Datum) (S R B b v N : Nat) :
    familyBank a ⟨S,R,B,b,v,N⟩ (ds.flatMap (P1TopDownPaidReusable.Datum.word a)) =
      r_inputT a ds S R B b v N := by
  funext j
  simp only [familyBank, r_inputT, f_entry, RepeatMachine.cfg, controlConfig,
    TapeEmbedding.config, P1TopDownPaidReusable.source]

end PCJ2bf639ce0c7c470f_Assembly
