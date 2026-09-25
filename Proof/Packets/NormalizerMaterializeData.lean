import Proof.Amplification.RecoveryFocusDock
import Proof.Packets.DedupMaterialReady
import Proof.Packets.MaskReverseReady
import Proof.Packets.NormalizerOrder
import Proof.Packets.ParityFilterReady

/-! Fixed tape wiring and concrete reserves for the complete normalization
pipeline. Bounds only pad erased work logs, never polynomial/source bytes. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

def records (raw : List (List Bool)) := raw.map PhysicalParityScan.supportRecord
def recordBits (bits : List Bool) := ClauseEquality.stream (PhysicalParityScan.supportRecord bits)
def distinctBits (raw : List (List Bool)) := raw.dedup.map recordBits
def candidates (raw : List (List Bool)) := raw.dedup.reverse

theorem recordBits_length (bits : List Bool) : (recordBits bits).length=2*bits.length+3 := by
  simp [recordBits,ParityFilter.support_stream,frame_length]

theorem dedup_records (raw : List (List Bool)) : (records raw).dedup=records raw.dedup :=
  List.dedup_map_of_injective PhysicalParityScan.supportRecord_injective raw

theorem source_eq (raw : List (List Bool)) : SuffixScan.stream (records raw)=ParityFilter.candidateStream raw := rfl

theorem distinct_flat (raw : List (List Bool)) : (distinctBits raw).flatten=SuffixScan.stream (records raw).dedup := by
  rw [dedup_records]
  unfold distinctBits recordBits records SuffixScan.stream
  rw [List.map_map]
  rfl

theorem distinct_reverse_flat (raw : List (List Bool)) :
    (distinctBits raw).reverse.flatten=ParityFilter.candidateStream (candidates raw) := by
  unfold distinctBits recordBits ParityFilter.candidateStream PhysicalParityScan.stream candidates
  rw [←List.map_reverse,List.map_map]
  rfl

theorem distinct_width (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∀ bits∈distinctBits raw,bits.length=2*B+3 := by
  intro bits hb
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hb
  rw [recordBits_length,hw row (List.mem_dedup.mp hr)]

theorem candidate_width (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∀ bits∈candidates raw,bits.length=B := by
  intro bits hb
  exact hw bits (List.mem_dedup.mp (List.mem_reverse.mp hb))

theorem selected_eq (raw : List (List Bool)) :
    ParityFilter.selected (records raw) (candidates raw)=NormalizerOrder.ordered raw := by
  unfold ParityFilter.selected NormalizerOrder.ordered candidates
  apply List.filter_congr
  intro bits _
  exact PhysicalCoefficientAlgebra.coefficient_map _ PhysicalParityScan.supportRecord_injective bits raw false

def probeCap (B : Nat) := 2*B+9
def scanCap (B M : Nat) := M*(2*probeCap B+5)+3
def reverseCap (B M : Nat) := MaskReverseReady.budget (2*B+3) M
def filterCap (B M : Nat) := ParityFilter.filterBudget B M M (probeCap B)
def countCap (B M : Nat) := 2*filterCap B M+2

def extraHeads : Fin 11→Nat := ![1,0,0,0,0,0,0,0,1,0,0]
def extraData (B M : Nat) : Fin 11→List Bool :=
  ![UnaryTemplate.tape (2*B+3),[],List.replicate (reverseCap B M) false,[false],[false],
    List.replicate (probeCap B) false,List.replicate (scanCap B M) false,[],CompareMachine.word 0,
    List.replicate (filterCap B M) false,List.replicate (countCap B M) false]

def reverseSlots : Fin 5→Fin 24 := ![13,2,14,11,15]
def filterSlots : Fin 12→Fin 24 := ![14,0,16,17,18,3,19,20,21,11,22,23]
theorem reverseSlots_injective : Function.Injective reverseSlots := by decide +kernel
theorem filterSlots_injective : Function.Injective filterSlots := by decide +kernel

noncomputable def dedupMachine := TapeEmbedding.machine 11 DedupMaterialReady.machine
noncomputable def reverseMachine := RecoveryFocus.machine reverseSlots MaskReverseReady.machine
noncomputable def filterMachine := RecoveryFocus.machine filterSlots ParityFilter.readyMachine
noncomputable def prefixMachine := Composition.machine dedupMachine reverseMachine
noncomputable def machine := Composition.machine prefixMachine filterMachine
noncomputable def dedupEntry (B : Nat) (raw : List (List Bool)) :=
  TapeEmbedding.config extraHeads (extraData B raw.length)
    (DedupMaterialReady.entry (SuffixScan.stream (records raw)) raw.length)
def started {t s : Nat} (p : Machine t s) (heads : Fin t→Nat) (tapes : Fin t→List Bool) : Configuration t s :=
  ⟨p.start,heads,tapes⟩
noncomputable def entry (B : Nat) (raw : List (List Bool)) :=
  started machine (dedupEntry B raw).heads (dedupEntry B raw).tapes

end PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
