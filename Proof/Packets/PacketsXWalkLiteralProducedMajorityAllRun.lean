import Proof.Packets.PacketsXWalkLiteralProducedMajorityPrepareRun
import Proof.Packets.PacketsXWalkTranscriptColumnAllRun

/-! Closed generation of the exact ordered all-candidate majority bank from
raw header/sample words, including every reserve and initialization stage. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache
open NormalizedFiniteTransport
noncomputable section
variable {population active depth n : Nat}
attribute [local irreducible] prepare WalkTranscriptColumn.allMachine

def all := RecoveryFocus.machine controllerSlots WalkTranscriptColumn.allMachine
def machine := Composition.machine prepare all
def budget (C w root population active depth n : Nat) (mask : List Bool) :=
  prepareBudget C w root population active depth n mask+1+WalkTranscriptColumn.allBudget C w population (n+1)

theorem all_run (C w d root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root (S C w) (R C w) wins)
    (hdepth : depth=SourceGradedRank.depth active)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (hfit : (population+1)^(d*(n+1))≤2^w) (hVisits : n+1≤2^w) (hCodes : 2^(n+1)≤2^w)
    (codeTail : List Bool) :
    ∃H A,Step machine (budget C w root population active depth n (List.ofFn (fun i=>decide (i∈mask))))
      (fun _=>0)
      (input C w root population active n (List.ofFn (fun i=>decide (i∈mask)))
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
        (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)) H A ∧
      A 704=PacketVector.bank (R C w) (List.ofFn (fun column : Fin (population+1)=>
        (Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active)
          wins 0 sample column).map (maskNat C))) := by
  obtain ⟨masters,work,first,_retained⟩:=prepare_run C w d root mask wins h hdepth sample hVisits hCodes codeTail
  have ready:=prefix_ready C w root mask wins sample codeTail masters work
  have driver:=prefix_driver C w root mask wins sample codeTail masters work
  have compatible:=MajorityComplete.Cold.ready_compatible C w n (WalkTranscriptColumn.allPolys mask wins sample 0)
    (WalkTranscriptColumn.allPolys_length mask wins sample 0) hCodes
  obtain ⟨B,last,word,_ready⟩:=WalkTranscriptColumn.all_run
    (MajorityComplete.Cold.masters C (R C w) (n+1) ((R C w)^2)) C w d root (S C w) (R C w)
    mask wins h sample hfit hVisits hCodes
    (by simpa only [WalkTranscriptColumn.allPolys_length] using compatible)
    (fun j=>prefixHeads n (workerSlots j))
    (fun j=>prefixBank C w root mask wins sample codeTail masters work (workerSlots j)) ready.2 ready.1
  have actual:=SourceDock.dock last controllerSlots controller_injective (prefixHeads n)
    (prefixBank C w root mask wins sample codeTail masters work)
    (controller_head_view _ driver.2) (controller_word_view (R C w) population _ driver.1)
  refine ⟨_,_,first.seq actual,?_⟩
  exact (install_slot controllerSlots controller_injective _ _ 471).trans word

end
end Theorem25Completion.WalkLiteralProducedMajority
