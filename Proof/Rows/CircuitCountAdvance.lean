import Proof.Rows.NativeCircuitPrepare

/-! Produce the actual fifth native header's unary circuit count while keeping
the original source cursor at the first circuit. Earlier fields are only skipped. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitCountAdvance
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_CircuitCountCopy
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitCountCopy.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_TopArity.machine

def heads (pos field count : Nat) (i : Fin 15):=if i=0 then pos else if i=2 then field else if i=14 then count else 0
def bank (source scratch field unary : List Bool) (U : Nat) (i : Fin 15):List Bool:=
 if i=0 then source else if i=1 then scratch else if i=2 then field else if i=3 then List.replicate U true
 else if i=4 then List.replicate (U+1) false else if i=14 then unary else List.replicate U false

def copy:=TapeEmbedding.machine 12 PCJ45bee56da9f34d5a_CircuitCountCopy.machine
-- Copy needs its capacity and log at3,4, with the remaining10 fresh reader tapes.
def rewindSlots:Fin 4→Fin 15:=![1,2,3,4]
def rewind:=RecoveryFocus.machine rewindSlots (PCJ45bee56da9f34d5a_HeaderRewind.machine 2)
def readSlots:Fin 13→Fin 15:=![2,5,6,7,8,9,10,11,12,13,14,4,3]
def read:=RecoveryFocus.machine readSlots PCJ45bee56da9f34d5a_TopArity.machine
def clear:=RecoveryFocus.machine rewindSlots (RecoveryScratchErase.resetMachine 2)
def machine:=Composition.machine (Composition.machine (Composition.machine copy rewind) read) clear

theorem copy_run (tag q L target N U : Nat) (tail : List Bool) :
 Step copy (PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target N) (heads 0 0 0)
  (bank (source tag q L target N tail) (List.replicate U false) (List.replicate U false) (List.replicate U false) U)
  (heads ((header tag q L target).length+(natWord N).length) (natWord N).length 0)
  (bank (source tag q L target N tail) (after tag q L target N (List.replicate U false))
   (ZeroPadding.pad U (natWord N)) (List.replicate U false) U) :=by
 have raw:=(PCJ45bee56da9f34d5a_CircuitCountCopy.run tag q L target N tail
  (List.replicate U false)).pad (fun i : Fin 3=>if i=2 then U else 0)
 have h:=raw.embed (fun _ :Fin 12=>0) (fun i : Fin 12=>bank (source tag q L target N tail)
  (List.replicate U false) (List.replicate U false) (List.replicate U false) U (i.natAdd 3))
 refine (h.congr_in ?_ ?_).congr ?_ ?_
 · funext i;fin_cases i <;>rfl
 · funext i;fin_cases i <;>simp [bank,tapes,Fin.addCases,ZeroPadding.pad]
 · funext i;fin_cases i <;>rfl
 · funext i;fin_cases i <;>first | rfl | exact ZeroPadding.pad_zero _

theorem rewind_run (source scratch field unary : List Bool) (U pos len : Nat) (hl : len≤U) :
 Step rewind (2*U+4) (heads pos len 0) (bank source scratch field unary U)
  (heads pos 0 0) (bank source scratch field unary U) :=by
 have h:=(PCJ45bee56da9f34d5a_HeaderRewind.run 2 (![0,len] :Fin 2→Nat)
  (![scratch,field] :Fin 2→List Bool) U (by intro i;fin_cases i <;>first | exact Nat.zero_le _ | exact hl)).dock
  rewindSlots (by decide) (heads pos len 0) (bank source scratch field unary U)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads rewindSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi
     have h2:i≠2:=fun he=>hi 1 he.symm
     by_cases h0:i=0 <;>simp [heads,h0,h2]
 · exact install_existing _ _ _ (by intro i;fin_cases i <;>rfl)

theorem read_run (source scratch : List Bool) (N U pos : Nat) (hU : PCPPQueryNatural.budget N<U) :
 Step read (2*PCPPQueryNatural.budget N+4*U+10) (heads pos 0 0)
  (bank source scratch (ZeroPadding.pad U (natWord N)) (List.replicate U false) U)
  (heads pos 0 1) (bank source scratch (ZeroPadding.pad U (natWord N)) (ZeroPadding.pad U (UnaryTemplate.tape N)) U) :=by
 have raw:=(PCJ45bee56da9f34d5a_TopArity.run N U [] hU).pad (fun i : Fin 13=>if i=0 then U else 0)
 simp only [List.append_nil] at raw
 have h:=raw.dock readSlots (by decide) (heads pos 0 0)
  (bank source scratch (ZeroPadding.pad U (natWord N)) (List.replicate U false) U)
  (by intro i;fin_cases i <;>rfl)
  (by intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads readSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi
     have h14:i≠14:=fun he=>hi 10 he.symm
     simp only [heads,if_neg h14]
 · apply HierarchyAllocation.install_eq readSlots (by decide)
   · intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm
   · intro i hi
     have h14:i≠14:=fun he=>hi 10 he.symm
     simp only [bank,if_neg h14]

theorem clear_run (source scratch field unary : List Bool) (U pos : Nat)
 (hs : scratch.length≤U) (hf : field.length≤U) :
 Step clear (2*U+4) (heads pos 0 1) (bank source scratch field unary U)
  (heads pos 0 1) (bank source (List.replicate U false) (List.replicate U false) unary U) :=by
 have h:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) (![scratch,field] :Fin 2→List Bool)
  (by intro i;fin_cases i <;>first | exact hs | exact hf))).dock rewindSlots (by decide)
  (heads pos 0 1) (bank source scratch field unary U)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
 · apply HierarchyAllocation.install_eq rewindSlots (by decide)
   · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
   · intro i hi
     have h1:i≠1:=fun he=>hi 0 he.symm
     have h2:i≠2:=fun he=>hi 1 he.symm
     simp only [bank,if_neg h1,if_neg h2]

def budget (tag q L target N U : Nat):=
 PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target N+2*PCPPQueryNatural.budget N+8*U+21

theorem run (tag q L target N U : Nat) (tail : List Bool)
 (hc : PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target N+2≤U)
 (hU : PCPPQueryNatural.budget N<U) :
 Step machine (budget tag q L target N U) (heads 0 0 0)
  (bank (source tag q L target N tail) (List.replicate U false) (List.replicate U false) (List.replicate U false) U)
  (heads ((header tag q L target).length+(natWord N).length) 0 1)
  (bank (source tag q L target N tail) (List.replicate U false) (List.replicate U false)
   (ZeroPadding.pad U (CompareMachine.word N)) U) :=by
 have hl:(natWord N).length≤U:=by rw [DecompositionSource.natWord_length];unfold PCJ45bee56da9f34d5a_CircuitCountCopy.budget at hc;omega
 have hs:(after tag q L target N (List.replicate U false)).length≤U:=by
  simp only [after,scratch,StablePartition.Workspace.overlay_length,UnaryTemplate.tape,
   List.length_append,List.length_cons,List.length_nil,List.length_replicate,max_le_iff]
  unfold PCJ45bee56da9f34d5a_CircuitCountCopy.budget at hc
  omega
 have hf:(ZeroPadding.pad U (natWord N)).length≤U:=by rw [ZeroPadding.pad_length];exact max_le (le_refl _) hl
 have first:=copy_run tag q L target N U tail
 have second:=rewind_run (source tag q L target N tail) (after tag q L target N (List.replicate U false))
  (ZeroPadding.pad U (natWord N)) (List.replicate U false) U
  ((header tag q L target).length+(natWord N).length) (natWord N).length hl
 have third:=read_run (source tag q L target N tail) (after tag q L target N (List.replicate U false)) N U
  ((header tag q L target).length+(natWord N).length) hU
 have last:=clear_run (source tag q L target N tail) (after tag q L target N (List.replicate U false))
  (ZeroPadding.pad U (natWord N)) (ZeroPadding.pad U (UnaryTemplate.tape N)) U
  ((header tag q L target).length+(natWord N).length) hs hf
 have h:=((first.seq second).seq third).seq last
 have hn:N+2≤U:=by unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget at hU;omega
 rw [PCJ45bee56da9f34d5a_NativeCircuitPrepare.count_eq N U hn] at h
 have he : ((PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target N+1+(2*U+4))+1+
  (2*PCPPQueryNatural.budget N+4*U+10))+1+(2*U+4)=budget tag q L target N U :=by unfold budget;omega
 simpa only [machine,he] using h
end
end PCJ45bee56da9f34d5a_CircuitCountAdvance
