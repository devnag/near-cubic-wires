import Proof.Rows.StreamPair

/-! Only the consumed stream/count/clock projections of the paired producer.
All other tapes remain opaque across the upcoming paid rewind. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_StreamPairPorts
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data)
open PCJ45bee56da9f34d5a_StreamPair
noncomputable section

theorem extraSlot (i :Fin 12):i.natAdd 110=PCJ45bee56da9f34d5a_CoefficientRun.offsetSlots (i.castAdd 1) :=by
 apply Fin.ext
 simp only [PCJ45bee56da9f34d5a_CoefficientRun.offsetSlots,Fin.val_castAdd,dif_pos i.isLt,Fin.val_natAdd]

theorem extra_word (d :Data) (B p w F U v o :Nat) (i :Fin 12):
 PCJ45bee56da9f34d5a_CoefficientRun.output d B p w F U v o [] (i.natAdd 110)=
 PCJ45bee56da9f34d5a_CoefficientRun.extra p w U o i :=by
 rw [extraSlot]
 unfold PCJ45bee56da9f34d5a_CoefficientRun.output
 rw [install_slot _ PCJ45bee56da9f34d5a_CoefficientRun.offsetSlots_injective]
 exact PCJ45bee56da9f34d5a_OffsetEmitter.out_away _ _ _ _ [] (i.castAdd 1)
  (by intro h;have hv:=congrArg Fin.val h;have hi:=i.isLt;change i.val=12 at hv;omega)

theorem extra_head (d :Data) (B p w o :Nat) (i :Fin 12):
 PCJ45bee56da9f34d5a_CoefficientRun.finalHeads d B p w o [] (i.natAdd 110)=0 :=by
 rw [extraSlot]
 unfold PCJ45bee56da9f34d5a_CoefficientRun.finalHeads
 rw [dockH_slot _ PCJ45bee56da9f34d5a_CoefficientRun.offsetSlots_injective]
 fin_cases i <;>rfl

def coefficientWord (d :Data) (B p w o :Nat):=
 PCJ45bee56da9f34d5a_FourfoldPowerData.stream d B p w 4++frame (binary w ((p-o)%p))
theorem coefficient_word (d :Data) (B p w F U v o :Nat):
 PCJ45bee56da9f34d5a_CoefficientRun.output d B p w F U v o [] 64=coefficientWord d B p w o :=by
 simpa only [List.nil_append,coefficientWord] using PCJ45bee56da9f34d5a_CoefficientRun.output_word d B p w F U v o []
theorem coefficient_head (d :Data) (B p w o :Nat):
 PCJ45bee56da9f34d5a_CoefficientRun.finalHeads d B p w o [] 64=(coefficientWord d B p w o).length :=by
 change PCJ45bee56da9f34d5a_CoefficientRun.finalHeads d B p w o []
  (PCJ45bee56da9f34d5a_CoefficientRun.offsetSlots 12)=_
 unfold PCJ45bee56da9f34d5a_CoefficientRun.finalHeads
 rw [dockH_slot _ PCJ45bee56da9f34d5a_CoefficientRun.offsetSlots_injective]
 change (([]++PCJ45bee56da9f34d5a_FourfoldPowerData.stream d B p w 4)++frame (binary w ((p-o)%p))).length=_
 rw [List.nil_append]
 rfl

def readSlots:Fin 6→Fin 250:=![107,122,192,124,248,249]
theorem readSlots_injective:Function.Injective readSlots:=by decide

variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)
 (T L target p w F U v o :Nat)

theorem read_words:
 (fun i=>output a r four sel I x T L target p w F U v o (readSlots i))=
 (![flags r I x,CompareMachine.word (flags r I x).length,
  coefficientWord (data a r four sel) (radix a r four sel) p w o,native r L target,
  List.replicate U true,List.replicate (U+1) false] :Fin 6→List Bool) :=by
 funext i;fin_cases i
 · rfl
 · rfl
 · exact coefficient_word (data a r four sel) (radix a r four sel) p w F U v o
 · rfl
 · exact extra_word (data a r four sel) (radix a r four sel) p w F U v o 10
 · exact extra_word (data a r four sel) (radix a r four sel) p w F U v o 11

theorem read_heads:
 (fun i=>outputHeads a r four sel I x L target p w o (readSlots i))=
 (![(flags r I x).length,(flags r I x).length+1,
  (coefficientWord (data a r four sel) (radix a r four sel) p w o).length,
  (native r L target).length,0,0] :Fin 6→Nat) :=by
 funext i;fin_cases i
 · rfl
 · rfl
 · exact coefficient_head (data a r four sel) (radix a r four sel) p w o
 · rfl
 · exact extra_head (data a r four sel) (radix a r four sel) p w o 10
 · exact extra_head (data a r four sel) (radix a r four sel) p w o 11

theorem prime_word:output a r four sel I x T L target p w F U v o 240=frame (binary w p) :=by
 exact extra_word (data a r four sel) (radix a r four sel) p w F U v o 2

theorem prime_head:outputHeads a r four sel I x L target p w o 240=0 :=by
 exact extra_head (data a r four sel) (radix a r four sel) p w o 2
end
end PCJ45bee56da9f34d5a_StreamPairPorts
