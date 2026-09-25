import Proof.Packets.WindowSeed
import Proof.Packets.PacketsXDescendingWindowLoop

/-! Literal equality between the physically seeded bank and the original
retained enumerator/scalar layout. Extra zero backing is retained physically. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def loopCaps (R : Nat) (i : Fin 62) : Nat :=
  if i=51 then R+3 else if i=44 ∨ i=59 ∨ i=61 then R else 0
def loopData (R v u M offset W target j : Nat) : Fin 62→List Bool :=
  Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool)
    (DescendingWindowLoop.A v u M offset target R 0 false false [] j)
    (fun _=>CompareMachine.word (2*W+1))
def loopHeads (v M offset target j : Nat) : Fin 62→Nat :=
  Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat) (DescendingWindowLoop.H v M offset target [] j) (fun _=>1)
def after (R v u M offset W target j : Nat) : Fin 69→List Bool :=
  Fin.addCases (m:=62) (n:=7) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (loopCaps R i) (loopData R v u M offset W target j i))
    (metadata R v u M offset W target)
def afterHeads (v M offset target j : Nat) : Fin 69→Nat :=
  Fin.addCases (m:=62) (n:=7) (motive:=fun _=>Nat) (loopHeads v M offset target j) (fun _=>0)

theorem produced_layout (R v u M offset W target : Nat) (hR : 1≤R) :
    produced R v u M offset W target=after R v u M offset W target 0 := by
  funext i
  fin_cases i <;>simp [produced,updates,initial,metadata,source,after,loopCaps,loopData,
    DescendingWindowLoop.A,DescendingWindowLoop.oldScratch,DescendingWindowLoop.oldNonzero,
    DescendingWindowLoop.oldGuard,DescendingWindowLoop.output,DescendingWindowSetup.A,
    CloseoutRowsModeWindowLayout.data,CloseoutRowsModeWindowLayout.extra,
    CloseoutRowsModeWindowLayout.scalars,CloseoutRowsModeWindowLayout.scalarCaps,
    CloseoutRowsModeWindowGuard.data,CloseoutRowsModeWindowGuard.extra,CloseoutRowsModeShift.data,
    CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryReusable.masterCaps,
    CloseoutRowsModeElementaryLayout.blank_eq,CloseoutRowsModeElementaryLayout.flatBlank,
    CloseoutRowsModeElementaryLayout.extra,CloseoutRowsModeElementaryLayout.metadata,
    Fin.addCases,ZeroPadding.pad,CompareMachine.word,hR]
  all_goals first
    | (rw [←List.replicate_succ]; congr 1; omega)
    | (rw [show R+3=(R+1)+2 by omega,List.replicate_add]; rfl)

theorem produced_heads (v M offset target : Nat) : H 1=afterHeads v M offset target 0 := by
  funext i
  fin_cases i <;>rfl

def emitted (v M offset W target : Nat) := DescendingWindowLoop.output v M offset target [] (2*W+1)

theorem after_output (R v u M offset W target : Nat) :
    after R v u M offset W target (2*W+1) 44=ZeroPadding.pad R (emitted v M offset W target) := by
  change ZeroPadding.pad R (CloseoutRowsModeElementaryReusable.paddedBlank v 0 M R
    (emitted v M offset W target) 44)=_
  rw [CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryLayout.blank_eq]
  change ZeroPadding.pad R (ZeroPadding.pad 0 (emitted v M offset W target))=_
  rw [ZeroPadding.pad_zero]

theorem after_heads (v M offset W target : Nat) (i : Fin 69) :
    afterHeads v M offset target (2*W+1) i=
      if i=44 then (emitted v M offset W target).length else if i=61 then 1 else 0 := by
  fin_cases i <;>rfl

theorem after_raw (R v u M offset W target j : Nat) :
    after R v u M offset W target j 50=List.replicate R true := by
  change ZeroPadding.pad 0 (CloseoutRowsModeElementaryReusable.paddedBlank v 0 M R
    (DescendingWindowLoop.output v M offset target [] j) 50)=_
  rw [CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryLayout.blank_eq]
  change ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate R true))=_
  simp only [ZeroPadding.pad_zero]

theorem after_log (R v u M offset W target j : Nat) :
    after R v u M offset W target j 51=List.replicate (R+3) false := by
  change ZeroPadding.pad (R+3) (CloseoutRowsModeElementaryReusable.paddedBlank v 0 M R
    (DescendingWindowLoop.output v M offset target [] j) 51)=_
  rw [CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryLayout.blank_eq]
  change ZeroPadding.pad (R+3) (ZeroPadding.pad 0 (List.replicate (R+1) false))=_
  rw [ZeroPadding.pad_zero,Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega)]

theorem after_private_lengths (R v u M offset W target : Nat)
    (hu : 2*u+1≤R) (hv : 2*v+1≤R) (hM : M≤R) (hW : 2*W+2≤R)
    (hout : (emitted v M offset W target).length≤R) :
    ∀j,(after R v u M offset W target (2*W+1) (privateSlot j)).length=R := by
  have hout' : (DescendingWindowLoop.output v M offset target [] (2*W+1)).length≤R:=hout
  intro j
  fin_cases j <;>simp [privateSlot,after,loopCaps,loopData,
    DescendingWindowLoop.A,DescendingWindowSetup.A,
    CloseoutRowsModeWindowLayout.data,CloseoutRowsModeWindowLayout.extra,
    CloseoutRowsModeWindowLayout.scalars,CloseoutRowsModeWindowLayout.scalarCaps,
    CloseoutRowsModeWindowGuard.data,CloseoutRowsModeWindowGuard.extra,CloseoutRowsModeShift.data,
    CloseoutRowsModeElementaryReusable.paddedBlank,CloseoutRowsModeElementaryReusable.masterCaps,
    CloseoutRowsModeElementaryLayout.blank_eq,CloseoutRowsModeElementaryLayout.flatBlank,
    CloseoutRowsModeElementaryLayout.extra,CloseoutRowsModeElementaryLayout.metadata,
    Fin.addCases,ZeroPadding.pad_length,CompareMachine.word,frame_length,SignedSortKey.binary_length]
  all_goals omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
