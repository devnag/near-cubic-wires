import Proof.Packets.PacketsXLiteralPairRecord
import Proof.PCP.PCPPairColdRun
import Proof.Rows.PhysicalFocusBoundary

/-! A cold physical native singleton-pair record from two framed binary
operands. The entire private workspace is produced by executed pair arithmetic;
zero inputs, including Nat.pair 0 0, use the same fixed machine. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.RepairOrdinary.SignedSortKey
noncomputable section

theorem pair_ready (left right : List Bool) :
    ∃ out : Fin 35→List Bool,
      Step PCPPairCold.machine (PCPPairCold.budget left right)
        (fun _=>0) (PCPPairCold.input left right) (fun _=>0) out ∧
      out 26=frame (binary (PCPPair.width left right) (Nat.pair (value left) (value right))) ∧
      out 31=[true] ∧ out 32=List.replicate (2*PCPPair.width left right+1) false := by
  obtain ⟨out,hpair,hout⟩ := PCPPair.pair_run left right
  have hp := CompetitorRationalProducts.bounded_focus PCPPairCold.pairSlots PCPPairCold.pair_injective
    _ _ _ hpair (PCPPairCold.prepared left right) (PCPPairCold.prepared_pair left right)
  have hwhole := ClockJoin.join _ _ _ _ _ _ _ (PCPPairCold.prepare_run left right) hp
  have whole : ClockJoin.ReadyRun PCPPairCold.machine (PCPPairCold.budget left right)
      (PCPPairCold.input left right)
      (install PCPPairCold.pairSlots (PCPPairCold.prepared left right) out) := by
    convert hwhole using 1 <;>first | rfl | (unfold PCPPairCold.budget;omega)
  obtain ⟨r,hr,ht,hh,hs⟩ := whole
  refine ⟨_,⟨r,hr,funext hh,ht,hs⟩,?_,?_,?_⟩
  · exact (install_slot PCPPairCold.pairSlots PCPPairCold.pair_injective _ _ 26).trans hout
  · rw [install_other PCPPairCold.pairSlots _ _ 31]
    · rfl
    · intro j he;have hv:=congrArg Fin.val he;simp [PCPPairCold.pairSlots] at hv;omega
  · rw [install_other PCPPairCold.pairSlots _ _ 32]
    · rfl
    · intro j he;have hv:=congrArg Fin.val he;simp [PCPPairCold.pairSlots] at hv;omega

def heads (pre : List Bool) (i : Fin 36) : Nat := if i=35 then pre.length else 0
def input (left right pre : List Bool) : Fin 36→List Bool :=
  Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool) (PCPPairCold.input left right) (fun _=>pre)
def recordSlots : Fin 4→Fin 36 := ![26,31,32,35]
def recordMachine := RecoveryFocus.machine recordSlots LiteralPairRecord.machine
def machine := Composition.machine (TapeEmbedding.machine 1 PCPPairCold.machine) recordMachine
def budget (left right : List Bool) := PCPPairCold.budget left right+1+
  LiteralPairRecord.budget (PCPPair.width left right) (Nat.pair (value left) (value right))

theorem run (left right pre : List Bool) : ∃ out : Fin 36→List Bool,
    Step machine (budget left right) (heads pre) (input left right pre)
      (heads (pre++ReflectedLiteralCache.singletonWord (Nat.pair (value left) (value right)))) out ∧
    out 35=pre++ReflectedLiteralCache.singletonWord (Nat.pair (value left) (value right)) := by
  obtain ⟨paired,hpair,hcode,hflag,hlog⟩ := pair_ready left right
  let middle : Fin 36→List Bool := Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool) paired (fun _=>pre)
  have first:=hpair.embed (fun _ : Fin 1=>pre.length) (fun _ : Fin 1=>pre)
  have he : (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>Nat)
      (fun _=>0) (fun _=>pre.length))=heads pre := by
    funext i;fin_cases i <;>rfl
  rw [he] at first
  obtain ⟨residue,_,hrecord⟩ := LiteralPairRecord.run
    (PCPPair.width left right) (Nat.pair (value left) (value right))
    (2*PCPPair.width left right+1) pre true (PCPPair.pair_bound left right) (by omega)
  let final := install recordSlots middle
    ![frame residue,[false],List.replicate (2*PCPPair.width left right+1) false,
      pre++ReflectedLiteralCache.singletonWord (Nat.pair (value left) (value right))]
  have last : Step recordMachine
      (LiteralPairRecord.budget (PCPPair.width left right) (Nat.pair (value left) (value right)))
      (heads pre) middle
      (heads (pre++ReflectedLiteralCache.singletonWord (Nat.pair (value left) (value right)))) final := by
    apply PhysicalFocusBoundary.focus hrecord recordSlots (by decide)
      (heads pre) _ middle final
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i
      · exact hcode.symm
      · exact hflag.symm
      · exact hlog.symm
      · rfl
    · intro i;fin_cases i <;>rfl
    · intro i;exact (install_slot recordSlots (by decide) middle _ i).symm
    · intro i hi
      constructor
      · have hn : i≠35 := by intro h;subst i;exact hi 3 rfl
        simp [heads,hn]
      · exact (install_other recordSlots middle _ i hi).symm
  refine ⟨final,first.seq last,?_⟩
  exact install_slot recordSlots (by decide) middle _ 3

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCold
