import Proof.Rows.SelectedPowerRun

/-! The selected coefficient cell's arity comes from the actual TOP payload;
its child-index driver comes from the retained private framed binary digit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerPrepare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopArity.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_TopIndex.machine

def bank (a B p w F U n index v key : Nat) (source out : List Bool):Fin 101→List Bool:=
 Fin.addCases (m:=99) (n:=2) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_SelectedPowerBank.bank a B p w F U n index source [] out)
  ![frame (binary v key),List.replicate v true]
def heads (len count index : Nat) (i :Fin 101):=if i=91 then count else if i=95 then index else if i=64 then len else 0

def aritySlots:Fin 13→Fin 101:=![94,31,32,33,34,35,36,37,38,39,91,63,62]
def indexSlots:Fin 9→Fin 101:=![100,31,32,33,34,99,95,62,63]
def arity:=RecoveryFocus.machine aritySlots PCJ45bee56da9f34d5a_TopArity.machine
def index:=RecoveryFocus.machine indexSlots PCJ45bee56da9f34d5a_TopIndex.machine

theorem compare_zero (U : Nat) (hU : 1≤U):ZeroPadding.pad U (CompareMachine.word 0)=List.replicate U false :=by
 change ZeroPadding.pad U (List.replicate 1 false)=_
 exact pad_replicate_false U 1 hU

theorem unary_zero (U : Nat) (hU : 2≤U):ZeroPadding.pad U (UnaryTemplate.tape 0)=List.replicate U false :=by
 change ZeroPadding.pad U (List.replicate 2 false)=_
 exact pad_replicate_false U 2 hU

theorem at62 (a B p w F U n index v key : Nat) (source out : List Bool) :
 bank a B p w F U n index v key source out 62=List.replicate U true :=by
 change PCJ45bee56da9f34d5a_SelectedPowerBank.bank a B p w F U n index source [] out 62=_
 exact PCJ45bee56da9f34d5a_SelectedPowerBank.at62 a B p w F U n index source [] out

theorem at63 (a B p w F U n index v key : Nat) (source out : List Bool) :
 bank a B p w F U n index v key source out 63=List.replicate (U+1) false :=by
 change PCJ45bee56da9f34d5a_SelectedPowerBank.bank a B p w F U n index source [] out 63=_
 exact PCJ45bee56da9f34d5a_SelectedPowerBank.at63 a B p w F U n index source [] out

theorem bank_away (a B p w F U n n' index index' v key : Nat) (source out : List Bool)
 (i :Fin 101) (hn : i≠91) (hi : i≠95) :
 bank a B p w F U n index v key source out i=bank a B p w F U n' index' v key source out i :=by
 revert hn hi
 refine Fin.addCases (m:=99) (n:=2) (fun j hj hk=>?_) (fun _ _ _=>?_) i
 · simp only [bank,Fin.addCases_left]
   revert hj hk
   refine Fin.addCases (m:=94) (n:=5) (fun k hk _=>?_) (fun k _ hk=>?_) j
   · simp only [PCJ45bee56da9f34d5a_SelectedPowerBank.bank,Fin.addCases_left,PCJ45bee56da9f34d5a_SelectedPowerBank.core]
     apply congrArg (ZeroPadding.pad (PCJ45bee56da9f34d5a_SelectedPowerBank.caps U k))
     revert hk
     refine Fin.addCases (m:=91) (n:=3) (fun _ _=>?_) (fun l hl=>?_) k
     · simp only [PCJ45bee56da9f34d5a_PowerBank.bank,Fin.addCases_left]
     · fin_cases l <;>first | exact False.elim (hl rfl) | rfl
   · fin_cases k <;>first | exact False.elim (hk rfl) | rfl
 · simp only [bank,Fin.addCases_right]

theorem heads_arity_away (len n n' index : Nat) (i :Fin 101) (hi : i≠91):
 heads len n index i=heads len n' index i :=by simp only [heads,if_neg hi]
theorem heads_index_away (len n index index' : Nat) (i :Fin 101) (hi : i≠95):
 heads len n index i=heads len n index' i :=by simp only [heads,if_neg hi]

theorem arity_run {n :Nat} (gs :List (ExactThresholdGate n)) (a B p w F U v key :Nat) (out :List Bool)
 (hu : PCPPQueryNatural.budget n<U) :
 Step arity (2*PCPPQueryNatural.budget n+4*U+10)
  (heads out.length 0 0) (bank a B p w F U 0 0 v key (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out)
  (heads out.length 1 0) (bank a B p w F U n 0 v key (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out) :=by
 have hn:n+2≤U:=by unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget at hu;omega
 have hz:=compare_zero U (by omega)
 have hc:=PCJ45bee56da9f34d5a_NativeCircuitPrepare.count_eq n U hn
 have h:=(PCJ45bee56da9f34d5a_TopArity.run n U (exactListWord gs) hu).dock aritySlots (by decide)
  (heads out.length 0 0) (bank a B p w F U 0 0 v key (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out)
  (by intro i;fin_cases i <;>rfl)
  (by
   intro i;fin_cases i
   all_goals dsimp only [aritySlots,indexSlots,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
   all_goals first
    | rfl
    | exact hz
    | exact at62 a B p w F U 0 0 v key _ out
    | exact at63 a B p w F U 0 0 v key _ out
    | change ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate U false))=List.replicate U false
      rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero])
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads aritySlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_arity_away _ 0 1 0 i (fun he=>hi 10 he.symm)
 · apply HierarchyAllocation.install_eq aritySlots (by decide)
   · intro i;fin_cases i
     all_goals dsimp only [aritySlots,indexSlots,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
     all_goals first
      | rfl
      | exact hc.symm
      | exact at62 a B p w F U n 0 v key _ out
      | exact at63 a B p w F U n 0 v key _ out
      | change ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate U false))=List.replicate U false
        rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]
   · intro i hi
     by_cases h95:i=95
     · subst i;rfl
     exact (bank_away a B p w F U 0 n 0 0 v key _ out i (fun he=>hi 10 he.symm) h95).symm

theorem index_run (a B p w F U n v key :Nat) (source out :List Bool)
 (hk : key<2^v) (hu : MatrixUnaryTemplate.budget v key<U) :
 Step index (MatrixUnaryTemplate.budget v key+2*U+5)
  (heads out.length 1 0) (bank a B p w F U n 0 v key source out)
  (heads out.length 1 1) (bank a B p w F U n key v key source out) :=by
 have h2:2≤U:=by unfold MatrixUnaryTemplate.budget at hu;omega
 have hz:=unary_zero U h2
 have h:=(PCJ45bee56da9f34d5a_TopIndex.run v key U hk hu).dock indexSlots (by decide)
  (heads out.length 1 0) (bank a B p w F U n 0 v key source out)
  (by intro i;fin_cases i <;>rfl)
  (by
   intro i;fin_cases i
   all_goals dsimp only [aritySlots,indexSlots,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
   all_goals first
    | rfl
    | exact hz
    | exact at62 a B p w F U n 0 v key _ out
    | exact at63 a B p w F U n 0 v key _ out
    | change ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate U false))=List.replicate U false
      rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero])
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads indexSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_index_away _ 1 0 1 i (fun he=>hi 6 he.symm)
 · apply HierarchyAllocation.install_eq indexSlots (by decide)
   · intro i;fin_cases i
     all_goals dsimp only [aritySlots,indexSlots,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
     all_goals first
      | rfl
      | exact at62 a B p w F U n key v key _ out
      | exact at63 a B p w F U n key v key _ out
      | change ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate U false))=List.replicate U false
        rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]
   · intro i hi
     by_cases h91:i=91
     · subst i;rfl
     exact (bank_away a B p w F U n n 0 key v key source out i h91 (fun he=>hi 6 he.symm)).symm
end
end PCJ45bee56da9f34d5a_SelectedPowerPrepare
