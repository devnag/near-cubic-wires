import Proof.Rows.CoefficientRun
import Proof.Rows.NativeFamilyFlags

/-! The actual native flag/count traversal and selected TOP coefficient
traversal run on one fixed pair of banks. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_StreamPair
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_UniformMinimumBounds
open PCJ45bee56da9f34d5a_NativeFlagsMeaning (circuits)
noncomputable section

def shift (m n :Nat) (i :Fin n):Fin (m+n):=i.natAdd m
theorem shift_injective (m n :Nat):Function.Injective (shift m n):=by
 intro i j h
 apply Fin.ext
 have hv:=congrArg Fin.val h
 simp only [shift,Fin.val_natAdd] at hv
 omega

theorem prepend {n s :Nat} {M :Machine n s} {fuel :Nat} {H H' :Fin n→Nat} {A A' :Fin n→List Bool}
 (h:Step M fuel H A H' A') (m :Nat) (P :Fin m→Nat) (T :Fin m→List Bool):
 Step (RecoveryFocus.machine (shift m n) M) fuel (Fin.addCases P H) (Fin.addCases T A)
  (Fin.addCases P H') (Fin.addCases T A') :=by
 have hh:=h.dock (shift m n) (shift_injective m n) (Fin.addCases P H) (Fin.addCases T A)
  (by intro i;simp only [shift,Fin.addCases_right]) (by intro i;simp only [shift,Fin.addCases_right])
 have outside (j :Fin m):∀k,shift m n k≠j.castAdd n:=by
  intro k hk
  have hv:=congrArg Fin.val hk
  have hj:=j.isLt
  simp only [shift,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega
 apply hh.congr
 · funext i
   refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) i
   · rw [dockH_other (shift m n) _ _ _ (outside j)]
     simp only [Fin.addCases_left]
   · simpa only [shift,Fin.addCases_right] using dockH_slot (shift m n) (shift_injective m n) (Fin.addCases P H) H' j
 · funext i
   refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) i
   · rw [install_other (shift m n) _ _ _ (outside j)]
     simp only [Fin.addCases_left]
   · simpa only [shift,Fin.addCases_right] using install_slot (shift m n) (shift_injective m n) (Fin.addCases T A) A' j

def first:=TapeEmbedding.machine 122 PCJ45bee56da9f34d5a_NativeFamilyFlags.machine
def second:=RecoveryFocus.machine (shift 128 122) PCJ45bee56da9f34d5a_CoefficientRun.machine
def machine:=Composition.machine first second

variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)

def native (L target :Nat):=PCJ45bee56da9f34d5a_NativeFamilyFlags.source 1 L target (circuits r)
def flags:=PCJ45bee56da9f34d5a_NativeFlags.word (circuits r) I x
def data:=PCJ45bee56da9f34d5a_ThresholdData.data a r four sel
def radix:=PCJ45bee56da9f34d5a_ThresholdData.base a r four sel

def flagStart (T L target :Nat):Fin 128→List Bool:=
 PCJ45bee56da9f34d5a_NativeFamilyCount.bank I x T 0 (native r L target) [] (List.replicate (U T r.q (T+1)) false)
def flagEnd (T L target :Nat):Fin 128→List Bool:=
 PCJ45bee56da9f34d5a_NativeFamilyCount.bank I x T (flags r I x).length (native r L target) (flags r I x)
  (ZeroPadding.pad (U T r.q (T+1)) (CompareMachine.word (circuits r).length))
def flagStartHeads:=PCJ45bee56da9f34d5a_NativeFamilyCount.heads 0 [] 0 0
def flagEndHeads (L target :Nat):=PCJ45bee56da9f34d5a_NativeFamilyCount.heads
 (native r L target).length (flags r I x) (flags r I x).length 1

def input (T L target p w F U v o :Nat):Fin 250→List Bool:=
 Fin.addCases (m:=128) (n:=122) (motive:=fun _=>List Bool) (flagStart r I x T L target)
  (PCJ45bee56da9f34d5a_CoefficientRun.bank (data a r four sel) 1 (radix a r four sel) p w F U v o [])
def output (T L target p w F U v o :Nat):Fin 250→List Bool:=
 Fin.addCases (m:=128) (n:=122) (motive:=fun _=>List Bool) (flagEnd r I x T L target)
  (PCJ45bee56da9f34d5a_CoefficientRun.output (data a r four sel) (radix a r four sel) p w F U v o [])
def inputHeads:Fin 250→Nat:=Fin.addCases (m:=128) (n:=122) (motive:=fun _=>Nat) flagStartHeads (PCJ45bee56da9f34d5a_CoefficientRun.heads 0)
def outputHeads (L target p w o :Nat):Fin 250→Nat:=
 Fin.addCases (m:=128) (n:=122) (motive:=fun _=>Nat) (flagEndHeads r I x L target)
  (PCJ45bee56da9f34d5a_CoefficientRun.finalHeads (data a r four sel) (radix a r four sel) p w o [])

theorem native_eq (L target :Nat):native r L target=
 (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target).nativeWord :=by
 unfold native PCJ45bee56da9f34d5a_NativeFamilyFlags.source PCJ45bee56da9f34d5a_CircuitCountCopy.source
 rw [PCJ45bee56da9f34d5a_NativeFlagsMeaning.native_stream]
 simp only [circuits,List.length_map,PCJd4d1d9d7d1fa4313_Production.Request.nativeWord]

theorem run (T L target p w F U v C P o :Nat)
 (hnative :(native r L target).length≤T)
 (hb :PCJ45bee56da9f34d5a_FourfoldPowerData.Bounds (data a r four sel) (radix a r four sel) p w F U v C P)
 (ho :o<p):
 Step machine (PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 1 r.q L target (circuits r).length T+1+
  ((4*P+27)+1+(6*U+10*w+28))) inputHeads (input a r four sel I x T L target p w F U v o)
  (outputHeads a r four sel I x L target p w o) (output a r four sel I x T L target p w F U v o) :=by
 have left:=(PCJ45bee56da9f34d5a_NativeFamilyFlags.run (circuits r) I x [] T 0 1 L target hnative).embed
  (PCJ45bee56da9f34d5a_CoefficientRun.heads 0)
  (PCJ45bee56da9f34d5a_CoefficientRun.bank (data a r four sel) 1 (radix a r four sel) p w F U v o [])
 simp only [List.nil_append,Nat.zero_add] at left
 have right:=prepend (PCJ45bee56da9f34d5a_CoefficientRun.run (data a r four sel) (radix a r four sel)
  p w F U v C P o hb ho []) 128 (flagEndHeads r I x L target) (flagEnd r I x T L target)
 exact left.seq right
end
end PCJ45bee56da9f34d5a_StreamPair
