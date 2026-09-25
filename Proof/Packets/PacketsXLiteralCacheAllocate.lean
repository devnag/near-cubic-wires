import Proof.Packets.CycleLiveSuccessor
import Proof.Packets.PacketsXLiteralPairCache

/-! Cold allocation of the complete reflected-cache loop bank. Inputs are
only actual raw R, unary tag and unary count. Every scratch cell, loop counter,
copy of the metadata, and reset log is written by an executed machine. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheAllocate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization Completion
noncomputable section

def heads (i : Fin 68) : Nat := if i=1 ∨ i=61 ∨ i=62 then 1 else 0

def budget (R tag count : Nat) := 4*R+2*tag+4*count+36

theorem local_copy (R n : Nat) : Step (UWalkUnary.machine true false) (2*n+6)
    (fun _=>0) ![UnaryTemplate.tape n,List.replicate R false,[]]
    (fun _=>0) ![UnaryTemplate.tape n,UWalkUnary.source R n,List.replicate (n+2) false] := by
  have h := (LiteralPairUnary.of_clock (UWalkUnary.ready true false (n+2) n)).pad (![0,R,0])
  have hc : UWalkUnary.source (n+2) n=UnaryTemplate.tape n := Theorem25Completion.CycleLiveSuccessor.source_eq n
  have hi : (fun i=>ZeroPadding.pad ((![0,R,0] : Fin 3→Nat) i) (UWalkUnary.input (n+2) n i))=
      ![UnaryTemplate.tape n,List.replicate R false,[]] := by
    funext i;fin_cases i <;>simp [UWalkUnary.input,hc,ZeroPadding.pad]
  have ho : (fun i=>ZeroPadding.pad ((![0,R,0] : Fin 3→Nat) i) (UWalkUnary.result true false (n+2) n i))=
      ![UnaryTemplate.tape n,UWalkUnary.source R n,List.replicate (n+2) false] := by
    funext i
    fin_cases i
    · change ZeroPadding.pad 0 (UWalkUnary.source (n+2) n)=UnaryTemplate.tape n
      simpa only [ZeroPadding.pad_zero] using hc
    · change ZeroPadding.pad R (UWalkUnary.output true false n)=UWalkUnary.source R n
      simp only [UWalkUnary.output,UWalkUnary.lead,Bool.toNat_false,Nat.add_zero,
        if_true,List.singleton_append,UWalkUnary.source,CompareMachine.word]
    · exact ZeroPadding.pad_zero _
  exact (h.congr_in rfl hi).congr rfl ho

-- BEGIN GENERATED STEPS

def extraHeads : Fin 6→Nat := ![1,0,0,0,0,0]

theorem heads_eq : heads=Fin.addCases (m:=62) (n:=6) (motive:=fun _=>Nat)
    (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat)
      (LiteralPairReusable.heads []) (fun _=>1)) extraHeads := by
  funext i;fin_cases i <;>rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheAllocate
