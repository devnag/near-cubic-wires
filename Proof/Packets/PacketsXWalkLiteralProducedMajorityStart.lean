import Proof.Packets.PacketsXWalkLiteralProducedMajorityFront

/-! The actual produced-walk output supplies every nonempty input to the
first majority segment; all additional742-arena fields start empty. -/
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
noncomputable section
abbrev R (C w : Nat) := WalkLiteralProducedReserve.R C w
abbrev S (C w : Nat) := WalkLiteralProducedReserve.S C w

def input (C w root population active n : Nat) (mask x y code : List Bool) : Fin 742→List Bool :=
  Fin.addCases (m:=566) (n:=176) (motive:=fun _=>List Bool)
    (WalkLiteralProducedReserve.input C w root population active n mask x y code) (fun _=>[])
def walkHeads (n : Nat) : Fin 742→Nat :=
  Fin.addCases (m:=566) (n:=176) (motive:=fun _=>Nat) (WalkLiteralProducedReserve.finalHeads n) (fun _=>0)
variable {population active depth n : Nat}
def walkBank (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) : Fin 742→List Bool :=
  Fin.addCases (m:=566) (n:=176) (motive:=fun _=>List Bool)
    (WalkLiteralProducedReserve.output C w root mask wins sample codeTail masters work) (fun _=>[])

theorem walk_high (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool)
    (i : Fin 742) (hi : 566 ≤ i.val) :
    walkBank C w root mask wins sample codeTail masters work i=[] ∧ walkHeads n i=0 := by
  revert hi
  refine Fin.addCases (m:=566) (n:=176) (fun j=>?_) (fun j=>?_) i
  · intro hi
    have hb:=j.isLt
    simp only [Fin.val_castAdd] at hi
    omega
  · intro _
    constructor <;>simp only [walkBank,walkHeads,Fin.addCases_right]

theorem walk_metadata (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    ∀j : Fin 5,
      walkBank C w root mask wins sample codeTail masters work (metadataSlots j)=
        MajorityComplete.Cold.input C (R C w) n [] ((j.castAdd 36).natAdd 137) ∧
      walkHeads n (metadataSlots j)=metadataHeads j := by
  obtain ⟨h0,h1,h2,h3⟩:=WalkLiteralProducedReserve.output_master_words C w root mask wins sample codeTail masters work
  obtain ⟨g0,g1,g2,g3⟩:=WalkLiteralProducedReserve.master_heads n
  have h4:=WalkLiteralProducedReserve.output_count C w root mask wins sample codeTail masters work
  have g4:=WalkLiteralProducedReserve.count_head n
  intro j;fin_cases j
  · exact ⟨h0,g0⟩
  · exact ⟨h1,g1⟩
  · exact ⟨h2,g2⟩
  · exact ⟨h3,g3⟩
  · exact ⟨h4,g4⟩

theorem walk_cold_pin (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    ∀j,
      walkBank C w root mask wins sample codeTail masters work (coldSlots j)=MajorityComplete.Cold.input C (R C w) n [] j ∧
      walkHeads n (coldSlots j)=MajorityComplete.Cold.inputHeads metadataHeads j := by
  intro j
  refine Fin.addCases (m:=137) (n:=41) (fun i=>?_) (fun i=>?_) j
  · rw [coldSlots,Fin.addCases_left]
    have h:=walk_high C w root mask wins sample codeTail masters work (majoritySlots i) (majority_range i).1
    simpa only [MajorityComplete.Cold.input,MajorityComplete.Cold.inputHeads,Fin.append,Fin.addCases_left,
      ite_self] using h
  · refine Fin.addCases (m:=5) (n:=36) (fun i=>?_) (fun i=>?_) i
    · simp only [coldSlots,Fin.addCases_left,Fin.addCases_right]
      simpa only [MajorityComplete.Cold.inputHeads,Fin.append,Fin.addCases_left,Fin.addCases_right]
        using walk_metadata C w root mask wins sample codeTail masters work i
    · simp only [coldSlots,Fin.addCases_right]
      have hi : 566 ≤ (⟨705+i.val,by have hb:=i.isLt;omega⟩ : Fin 742).val := by dsimp;omega
      have h:=walk_high C w root mask wins sample codeTail masters work _ hi
      have hdata : MajorityComplete.Cold.input C (R C w) n [] ((i.natAdd 5).natAdd 137)=[] := by
        fin_cases i <;>rfl
      simpa only [hdata,MajorityComplete.Cold.inputHeads,Fin.append,Fin.addCases_right] using h

private theorem visit_rawS (rank R L S : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15→List Bool) (work : Fin 299→List Bool) (transcript : List Bool) :
    WalkLiteralVisit.A rank R L S v code palette work transcript 329=List.replicate S true := rfl

attribute [local irreducible] WalkLiteralProducedReserve.finalHeads WalkLiteralProduced.finalHeads
  WalkLiteralProducedReserve.output walkBank walkHeads

theorem walk_rawS (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    walkBank C w root mask wins sample codeTail masters work 424=List.replicate (S C w) true ∧ walkHeads n 424=0 := by
  have h1 : (424 : Fin 742)=(424 : Fin 566).castAdd 176 := rfl
  have h2 : (424 : Fin 566)=(WalkLiteralProduced.coldSlots 329).castAdd 133 := rfl
  constructor
  · rw [h1,walkBank,Fin.addCases_left,h2,WalkLiteralProducedReserve.output,Fin.addCases_left,
      install_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]
    have h3 : (329 : Fin 333)=(329 : Fin 332).castAdd 1 := rfl
    rw [h3,Fin.addCases_left]
    exact visit_rawS _ _ _ _ _ _ _ _ _
  · rw [h1,walkHeads,Fin.addCases_left,h2,WalkLiteralProducedReserve.finalHeads,Fin.addCases_left,
      WalkLiteralProduced.finalHeads,dockH_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]
    rfl

theorem walk_front (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    Step front (frontBudget (S C w) n) (walkHeads n) (walkBank C w root mask wins sample codeTail masters work)
      (scalarHeads (walkHeads n)) (scalarBank C (R C w) n (zeroBank (S C w) (walkBank C w root mask wins sample codeTail masters work))) := by
  have hm:=walk_cold_pin C w root mask wins sample codeTail masters work
  have hs:=walk_rawS C w root mask wins sample codeTail masters work
  have ht:=walk_high C w root mask wins sample codeTail masters work 567 (by decide)
  have hl:=walk_high C w root mask wins sample codeTail masters work 741 (by decide)
  apply front_run C (R C w) (S C w) n
  · intro i;fin_cases i
    · exact ht.2
    · exact hs.2
    · exact hl.2
  · exact hs.1
  · exact ht.1
  · exact hl.1
  · exact fun i=>(hm i).2
  · exact fun i=>(hm i).1

end
end Theorem25Completion.WalkLiteralProducedMajority
