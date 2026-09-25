import Proof.Rows.NativeCircuitSkip

/-! Parse the actual native circuit count, skip its TOP frame, and return a
cold parser bank with the physical padded count ready for the bottom loop. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeCircuitPrepare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_NativeCircuitCount
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeCircuitCount.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeCircuitSkip.field
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeCircuitSkip.skipTop
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeCircuitSkip.erase

def machine := Composition.machine
 (Composition.machine (Composition.machine PCJ45bee56da9f34d5a_NativeCircuitCount.machine
  PCJ45bee56da9f34d5a_NativeCircuitSkip.field) PCJ45bee56da9f34d5a_NativeCircuitSkip.skipTop)
 PCJ45bee56da9f34d5a_NativeCircuitSkip.erase

attribute [local irreducible] machine

def budget (n U t : Nat) :=2*PCPPQueryNatural.budget n+6*U+2*natBitLength n+2*t+21

theorem unary_eq (n : Nat) :
 ZeroPadding.pad (n+2) (CompareMachine.word n)=UnaryTemplate.tape n := by
 simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem count_eq (n U : Nat) (hn : n+2≤U) :
 ZeroPadding.pad U (UnaryTemplate.tape n)=ZeroPadding.pad U (CompareMachine.word n) := by
 rw [←unary_eq]
 exact MatrixBucketRootPower.pad_pad (n+2) U _ hn

theorem scratch_bound (n U : Nat) (hU : PCPPQueryNatural.budget n<U) :
 (ZeroPadding.pad U (PCJ45bee56da9f34d5a_CircuitCountCopy.scratch n [])).length≤U := by
 have hb : natBitLength n+2≤U := by
  unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget at hU
  omega
 rw [ZeroPadding.pad_length]
 apply max_le (le_refl U)
 simp only [PCJ45bee56da9f34d5a_CircuitCountCopy.scratch,StablePartition.Workspace.overlay_length,
  UnaryTemplate.tape,List.length_cons,List.length_append,List.length_replicate,List.length_nil,Nat.max_zero]
 omega

theorem run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q n : Nat)
 (top tail framed out : List Bool) (hU : PCPPQueryNatural.budget n<U) :
 Step machine (budget n U top.length)
  (heads 0 out Q 0)
  (bank live x w H R U (natWord n++frame top++tail) (List.replicate H false) framed out (List.replicate U false) Q)
  (heads ((natWord n).length+(frame top).length) out Q 1)
  (bank live x w H R U (natWord n++frame top++tail) (List.replicate H false) framed out
    (ZeroPadding.pad U (CompareMachine.word n)) Q) := by
 have hn : n+2≤U := by
  unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget at hU
  omega
 have first:=PCJ45bee56da9f34d5a_NativeCircuitCount.run live x w H R U Q n
  (frame top++tail) (List.replicate H false) framed out hU
 rw [count_eq n U hn] at first
 have field:=PCJ45bee56da9f34d5a_NativeCircuitSkip.field_run live x w H R U Q n
  (frame top++tail) framed out (ZeroPadding.pad U (CompareMachine.word n))
 have middle:=first.seq field
 have topRun:=PCJ45bee56da9f34d5a_NativeCircuitSkip.frame_run live x w H R U Q n
  top tail framed out (ZeroPadding.pad U (CompareMachine.word n))
  (ZeroPadding.pad U (PCJ45bee56da9f34d5a_CircuitCountCopy.scratch n []))
 simp only [List.append_assoc] at topRun
 have afterTop:=middle.seq topRun
 have last:=PCJ45bee56da9f34d5a_NativeCircuitSkip.erase_run live x w H R U Q
  ((natWord n).length+(frame top).length) (natWord n++frame top++tail) framed out
  (ZeroPadding.pad U (CompareMachine.word n))
  (ZeroPadding.pad U (PCJ45bee56da9f34d5a_CircuitCountCopy.scratch n [])) (scratch_bound n U hU)
 simp only [List.append_assoc] at last
 have h:=afterTop.seq last
 have hf : ((2*PCPPQueryNatural.budget n+4*U+10)+1+(2*natBitLength n+3))+1+(2*top.length+1)+1+(2*U+4)=
   budget n U top.length := by unfold budget;omega
 simpa only [machine,List.append_assoc,hf] using h
end
end PCJ45bee56da9f34d5a_NativeCircuitPrepare
