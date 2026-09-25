import Proof.Rows.StreamCompare

/-! One actual THR traversal: native gates produce flags/count; selected TOP
children produce scaled coefficients; paid rewind joins the modular comparator.
Initial private masters, including the physically constructed canonical B,
remain the explicit input bank of this consumer. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_ThresholdTraversal
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_StreamPair
open PCJ45bee56da9f34d5a_StreamPairPorts
noncomputable section

def first:=TapeEmbedding.machine 4 PCJ45bee56da9f34d5a_StreamPair.machine
def prepare:=TapeEmbedding.machine 4 PCJ45bee56da9f34d5a_StreamReady.machine
def machine:=Composition.machine (Composition.machine first prepare) PCJ45bee56da9f34d5a_StreamCompare.machine
def initialHeads:=PCJ45bee56da9f34d5a_StreamCompare.heads inputHeads

theorem initialHeads_le:∀i :Fin 254,initialHeads i≤1:=by decide

variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)
 {cutoff :Nat} (prime :PrimeIndex cutoff) (o :Fin prime.val) (T L target w F U v C P :Nat)

def budget:=((PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 1 r.q L target
 (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r).length T+1+((4*P+27)+1+(6*U+10*w+28)))+1+(2*U+6))+1+
 FinalPrimeThresholdRow.rowFuel w (PCJ45bee56da9f34d5a_StreamCompare.count a r sel I x)
def input:=PCJ45bee56da9f34d5a_StreamCompare.bank w
 (PCJ45bee56da9f34d5a_StreamPair.input a r four sel I x T L target prime.val w F U v o.val)

theorem run (hnative :(native r L target).length≤T)
 (hb :PCJ45bee56da9f34d5a_FourfoldPowerData.Bounds (data a r four sel) (radix a r four sel) prime.val w F U v C P)
 (hQ :(flags r I x).length+1≤U)
 (hcs :(coefficientWord (data a r four sel) (radix a r four sel) prime.val w o.val).length≤U)
 (hs :(native r L target).length≤U):
 Step machine (budget a r sel I x T L target w U P) initialHeads
  (input a r four sel I x prime o T L target w F U v)
  (PCJ45bee56da9f34d5a_StreamCompare.outputHeads a r four sel I x prime o L target w)
  (PCJ45bee56da9f34d5a_StreamCompare.output a r four sel I x prime o T L target w F U v) :=by
 have one:=(PCJ45bee56da9f34d5a_StreamPair.run a r four sel I x T L target prime.val w F U v C P o.val
  hnative hb o.isLt).embed (fun _ :Fin 4=>0) (PCJ45bee56da9f34d5a_StreamCompare.registers w)
 have two:=(PCJ45bee56da9f34d5a_StreamReady.run a r four sel I x T L target prime.val w F U v o.val hQ hcs hs).embed
  (fun _ :Fin 4=>0) (PCJ45bee56da9f34d5a_StreamCompare.registers w)
 have hc:2*w+2≤U+1:=by have h:=hb.capacity;nlinarith [Nat.zero_le (w*w)]
 have three:=PCJ45bee56da9f34d5a_StreamCompare.run a r four sel I x prime o T L target w F U v hb.prime_fit hc
 exact (one.seq two).seq three
end
end PCJ45bee56da9f34d5a_ThresholdTraversal
