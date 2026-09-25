import Proof.Rows.StreamReady
import Proof.Rows.ThresholdActualCompare

/-! Dock the exact modular comparator onto the produced, paid-rewound
native flag/count and selected coefficient streams. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_StreamCompare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_StreamPair
open PCJ45bee56da9f34d5a_StreamPairPorts
noncomputable section

def registers (w :Nat):Fin 4→List Bool:=![frame (binary w 0),frame (binary w 0),[false],[false]]
def bank (w :Nat) (A :Fin 250→List Bool):Fin 254→List Bool:=
 Fin.addCases (m:=250) (n:=4) (motive:=fun _=>List Bool) A (registers w)
def heads (H :Fin 250→Nat):Fin 254→Nat:=
 Fin.addCases (m:=250) (n:=4) (motive:=fun _=>Nat) H (fun _=>0)
def slots:Fin 9→Fin 254:=![250,251,240,252,107,192,249,122,253]
theorem slots_injective:Function.Injective slots:=by decide
def machine:=RecoveryFocus.machine slots FinalPrimeThresholdRow.whole

variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)
 {cutoff :Nat} (prime :PrimeIndex cutoff) (o :Fin prime.val) (T L target w F U v :Nat)

def bits:=occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x
def count:=(PCJ45bee56da9f34d5a_ExpandedThresholdStream.terms a r sel (bits r I x)).length+1
def verdict:=decide (LiveRows.modularOffset (thresholdFourfoldOccurrences r) I x
 (ThresholdRows.equation a r sel) prime.val=o.val)
def localOutput:Fin 9→List Bool:=
 let s:=PCJ45bee56da9f34d5a_ThresholdCompare.state prime.val w
  (PCJ45bee56da9f34d5a_ExpandedThresholdStream.equation a r sel (bits r I x) o.val)
  (PCJ45bee56da9f34d5a_ExpandedThresholdStream.input a r sel (bits r I x))
 PCJ45bee56da9f34d5a_ThresholdCompare.bank prime.val w (U+1) (count a r sel I x) (flags r I x)
  (coefficientWord (data a r four sel) (radix a r four sel) prime.val w o.val)
  (FinalPrimeRow.residueWord s) s.2.1 s.2.2 (verdict a r sel I x prime o)
def output:Fin 254→List Bool:=install slots
 (bank w (PCJ45bee56da9f34d5a_StreamPair.output a r four sel I x T L target prime.val w F U v o.val))
 (localOutput a r four sel I x prime o w U)
def outputHeads:Fin 254→Nat:=dockH slots
 (heads (PCJ45bee56da9f34d5a_StreamReady.heads
  (PCJ45bee56da9f34d5a_StreamPair.outputHeads a r four sel I x L target prime.val w o.val)))
 (PCJ45bee56da9f34d5a_ThresholdCompare.finalHeads w (count a r sel I x))

theorem count_eq:(flags r I x).length=count a r sel I x :=by
 unfold PCJ45bee56da9f34d5a_StreamPair.flags count bits
 rw [PCJ45bee56da9f34d5a_NativeFlagsMeaning.word_eq a r sel]
 simp only [List.length_append,List.length_map,List.length_singleton]

theorem run (hpw :2*prime.val≤2^w) (hU :2*w+2≤U+1):
 Step machine (FinalPrimeThresholdRow.rowFuel w (count a r sel I x))
 (heads (PCJ45bee56da9f34d5a_StreamReady.heads
  (PCJ45bee56da9f34d5a_StreamPair.outputHeads a r four sel I x L target prime.val w o.val)))
 (bank w (PCJ45bee56da9f34d5a_StreamPair.output a r four sel I x T L target prime.val w F U v o.val))
 (outputHeads a r four sel I x prime o L target w)
 (output a r four sel I x prime o T L target w F U v) :=by
 let H:=PCJ45bee56da9f34d5a_StreamPair.outputHeads a r four sel I x L target prime.val w o.val
 let A:=PCJ45bee56da9f34d5a_StreamPair.output a r four sel I x T L target prime.val w F U v o.val
 have hw:=read_words a r four sel I x T L target prime.val w F U v o.val
 have hq:=count_eq a r sel I x
 have hprime:= (PCJ45bee56da9f34d5a_StreamReady.head_other H 240 (by decide)).trans
  (prime_head a r four sel I x L target prime.val w o.val)
 have h:=PCJ45bee56da9f34d5a_ThresholdActualCompare.run a r four sel I x prime o w (U+1) hpw hU
 have hh:=h.dock slots slots_injective (heads (PCJ45bee56da9f34d5a_StreamReady.heads H)) (bank w A)
  (by
   intro i;fin_cases i
   · rfl
   · rfl
   · exact hprime
   · rfl
   · exact PCJ45bee56da9f34d5a_StreamReady.head_slots H 0
   · exact PCJ45bee56da9f34d5a_StreamReady.head_slots H 2
   · exact PCJ45bee56da9f34d5a_StreamReady.head_slots H 5
   · exact PCJ45bee56da9f34d5a_StreamReady.head_slots H 1
   · rfl)
  (by
   intro i;fin_cases i
   · rfl
   · rfl
   · exact prime_word a r four sel I x T L target prime.val w F U v o.val
   · rfl
   · exact congrFun hw 0
   · exact congrFun hw 2
   · exact congrFun hw 5
   · change A 122=CompareMachine.word (count a r sel I x)
     have hc:A 122=CompareMachine.word (flags r I x).length:=congrFun hw 1
     rw [hq] at hc
     exact hc
   · rfl)
 exact hh

theorem output_verdict:output a r four sel I x prime o T L target w F U v 253=[verdict a r sel I x prime o] :=by
 change output a r four sel I x prime o T L target w F U v (slots 8)=_
 unfold output
 rw [install_slot slots slots_injective]
 rfl

theorem output_verdict_head:outputHeads a r four sel I x prime o L target w 253=0 :=by
 change outputHeads a r four sel I x prime o L target w (slots 8)=_
 unfold outputHeads
 rw [dockH_slot slots slots_injective]
 rfl
end
end PCJ45bee56da9f34d5a_StreamCompare
