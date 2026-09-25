import Proof.Rows.OffsetNegation
import Proof.Rows.ResidueScaleCell
import Proof.Rows.NativeCircuitCount

/-! Reusable binary final-offset emitter: copy five bounded masters, negate,
append one framed residue without scanning the output, and clear all workers. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 20000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_OffsetEmitter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ExtIncidence SignedSortKey
noncomputable section

def palette (p w o :Nat):Fin 5→List Bool:=![frame (binary w 0),frame (binary w 0),frame (binary w p),[false],frame (binary w o)]
def bank (P W :Fin 5→List Bool) (U :Nat) (out :List Bool) (i :Fin 13):List Bool:=
 if h:i.val<5 then P ⟨i.val,h⟩ else
 if h:i.val<10 then W ⟨i.val-5,by omega⟩ else
 if i=10 then List.replicate U true else
 if i=11 then List.replicate (U+1) false else out

theorem out_away (P W :Fin 5→List Bool) (U :Nat) (out out' :List Bool) (i :Fin 13) (hi :i≠12):
 bank P W U out i=bank P W U out' i :=by
 by_cases h5:i.val<5
 · simp only [bank,dif_pos h5]
 by_cases h10:i.val<10
 · simp only [bank,dif_neg h5,dif_pos h10]
 have h:i=10 ∨ i=11:=by
  have hv:i.val≠12:=fun he=>hi (Fin.ext he)
  have hh:i.val=10 ∨ i.val=11:=by omega
  exact hh.imp Fin.ext Fin.ext
 rcases h with rfl | rfl <;>rfl

theorem workers_away (P W W' :Fin 5→List Bool) (U :Nat) (out :List Bool) (i :Fin 13)
 (hi :i.val<5 ∨ 10 ≤ i.val):bank P W U out i=bank P W' U out i :=by
 rcases hi with h | h
 · simp only [bank,dif_pos h]
 · simp only [bank,dif_neg (show ¬i.val<5 by omega),dif_neg (show ¬i.val<10 by omega)]

def cold (P :Fin 5→List Bool) (U :Nat) (out :List Bool):=bank P (fun _=>List.replicate U false) U out
def warm (P :Fin 5→List Bool) (U :Nat) (out :List Bool):=bank P (fun i=>ZeroPadding.pad U (P i)) U out
def results (p w U o :Nat) (i :Fin 5):=ZeroPadding.pad U (PCJ45bee56da9f34d5a_OffsetNegation.output p w (U+1) o (i.castAdd 1))
def heads (len pos :Nat) (i :Fin 13):=if i=12 then len else if i=5 then pos else 0

def choice (i :Fin 5):Option (Fin 5):=some i
def negSlots:Fin 6→Fin 13:=![5,6,7,8,9,11]
def copySlots:Fin 2→Fin 13:=![5,12]
def clearSlots:Fin 7→Fin 13:=![5,6,7,8,9,10,11]
def fanout:=TapeEmbedding.machine 1 (NativeFanout.machine choice)
def evaluate:=RecoveryFocus.machine negSlots PCJ45bee56da9f34d5a_OffsetNegation.machine
def append:=RecoveryFocus.machine copySlots CloseoutRowsTouching.FrameStream.machine
def clear:=RecoveryFocus.machine clearSlots (PCJ45bee56da9f34d5a_HeaderRewind.clear 5)
def machine:=Composition.machine (Composition.machine (Composition.machine fanout evaluate) append) clear

theorem fanout_run (P :Fin 5→List Bool) (U :Nat) (out :List Bool) (hP :∀i,(P i).length≤U):
 Step fanout (2*U+4) (heads out.length 0) (cold P U out) (heads out.length 0) (warm P U out) :=by
 have fo:=(NativeFanout.reusable choice P U hP).embed (fun _ :Fin 1=>out.length) (fun _=>out)
 have first:Step fanout (2*U+4) (heads out.length 0) (cold P U out) (heads out.length 0) (warm P U out):=by
  refine (fo.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl
 exact first


theorem evaluate_run (p w U o :Nat) (out :List Bool) (hU :2*w+2≤U):
 Step evaluate (8*w+11) (heads out.length 0) (warm (palette p w o) U out)
  (heads out.length 0) (bank (palette p w o) (results p w U o) U out) :=by
 let P:=palette p w o
 have ng:=(PCJ45bee56da9f34d5a_OffsetNegation.run p w (U+1) o (by omega)).pad (fun i :Fin 6=>if i=5 then 0 else U)
 have nd:=ng.dock negSlots (by decide) (heads out.length 0) (warm P U out)
  (by intro i;fin_cases i <;>rfl)
  (by intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm)
 have second:Step evaluate (8*w+11) (heads out.length 0) (warm P U out)
  (heads out.length 0) (bank P (results p w U o) U out):=by
  apply nd.congr
  · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  · apply HierarchyAllocation.install_eq negSlots (by decide)
    · intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm
    · intro i hi
      have hbound:i.val<5 ∨ 10 ≤ i.val:=by
       fin_cases i
       all_goals first
        | decide
        | exact False.elim (hi 0 rfl)
        | exact False.elim (hi 1 rfl)
        | exact False.elim (hi 2 rfl)
        | exact False.elim (hi 3 rfl)
        | exact False.elim (hi 4 rfl)
      exact workers_away P (results p w U o) (fun j=>ZeroPadding.pad U (P j)) U out i hbound
 exact second


theorem append_run (p w U o :Nat) (out :List Bool) (hp :0<p) (hpw :2*p≤2^w) (ho :o<p):
 Step append (2*w+1) (heads out.length 0) (bank (palette p w o) (results p w U o) U out)
  (heads (out++frame (binary w ((p-o)%p))).length (2*w+1))
  (bank (palette p w o) (results p w U o) U (out++frame (binary w ((p-o)%p)))) :=by
 let P:=palette p w o
 let bits:=binary w ((p-o)%p)
 have bl:bits.length=w:=binary_length _ _
 have word:results p w U o 0=ZeroPadding.pad U (frame bits):=by
  change ZeroPadding.pad U (frame (FinalPrimeRow.residueWord (FinalPrimeNegate.negState p w (binary w o))))=_
  rw [PCJ45bee56da9f34d5a_OffsetNegation.word_eq p w o hp hpw ho]
 obtain ⟨r,hr,hf,_⟩:=CloseoutRowsTouching.FrameStream.copy_run [] bits [] out
 have cp:Step CloseoutRowsTouching.FrameStream.machine (2*w+1)
  (![0,out.length] :Fin 2→Nat) ![frame bits,out]
  (![2*w+1,(out++frame bits).length] :Fin 2→Nat) ![frame bits,out++frame bits]:=by
  have h:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  simpa only [CloseoutRowsTouching.FrameStream.cfg,List.nil_append,List.append_nil,List.length_nil,
   Nat.zero_add,List.length_append,frame_length,bl] using h
 have cd:=(cp.pad (![U,0] :Fin 2→Nat)).dock copySlots (by decide)
  (heads out.length 0) (bank P (results p w U o) U out)
  (by intro i;fin_cases i <;>rfl)
  (by intro i;fin_cases i;exact word;exact (ZeroPadding.pad_zero _).symm)
 have third:Step append (2*w+1) (heads out.length 0) (bank P (results p w U o) U out)
  (heads (out++frame bits).length (2*w+1)) (bank P (results p w U o) U (out++frame bits)):=by
  apply cd.congr
  · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads copySlots (by decide)
    · intro i;fin_cases i <;>rfl
    · intro i hi
      have h5:i≠5:=fun he=>hi 0 he.symm
      have h12:i≠12:=fun he=>hi 1 he.symm
      simp only [heads,if_neg h5,if_neg h12]
  · apply HierarchyAllocation.install_eq copySlots (by decide)
    · intro i;fin_cases i
      · exact word
      · exact (ZeroPadding.pad_zero _).symm
    · intro i hi
      exact out_away P (results p w U o) U _ _ i (fun he=>hi 1 he.symm)
 exact third


theorem clear_run (P W :Fin 5→List Bool) (U pos :Nat) (out :List Bool)
 (hpos :pos≤U) (hW :∀i,(W i).length≤U):
 Step clear (4*U+9) (heads out.length pos) (bank P W U out)
  (heads out.length 0) (cold P U out) :=by
 let WH:Fin 5→Nat:=![pos,0,0,0,0]
 have wh:∀i,WH i≤U:=by intro i;fin_cases i <;>simp [WH];omega
 have cl:=(PCJ45bee56da9f34d5a_HeaderRewind.clear_run 5 WH (W) U wh hW).dock
  clearSlots (by decide) (heads out.length (pos)) (bank P (W) U out)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 have fourth:Step clear (4*U+9) (heads out.length (pos)) (bank P (W) U out)
  (heads out.length 0) (cold P U out):=by
  apply cl.congr
  · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads clearSlots (by decide)
    · intro i;fin_cases i <;>rfl
    · intro i hi
      have h5:i≠5:=fun he=>hi 0 he.symm
      simp only [heads,if_neg h5]
  · apply HierarchyAllocation.install_eq clearSlots (by decide)
    · intro i;fin_cases i <;>rfl
    · intro i hi
      have hbound:i.val<5 ∨ 10 ≤ i.val:=by
       fin_cases i
       all_goals first
        | decide
        | exact False.elim (hi 0 rfl)
        | exact False.elim (hi 1 rfl)
        | exact False.elim (hi 2 rfl)
        | exact False.elim (hi 3 rfl)
        | exact False.elim (hi 4 rfl)
      exact workers_away P (fun _=>List.replicate U false) W U out i hbound
 exact fourth


theorem run (p w U o :Nat) (out :List Bool) (hp :0<p) (hpw :2*p≤2^w) (ho :o<p) (hU :2*w+2≤U):
 Step machine (6*U+10*w+28) (heads out.length 0) (cold (palette p w o) U out)
  (heads (out++frame (binary w ((p-o)%p))).length 0) (cold (palette p w o) U (out++frame (binary w ((p-o)%p)))) :=by
 let P:=palette p w o
 let bits:=binary w ((p-o)%p)
 have hP:∀i,(P i).length≤U:=by
  intro i;fin_cases i <;>simp [P,palette,frame_length,binary_length] <;>omega
 have hW:∀i,(results p w U o i).length≤U:=by
  intro i;rw [results,ZeroPadding.pad_length]
  exact max_le (le_refl _) ((PCJ45bee56da9f34d5a_OffsetNegation.output_lengths p w (U+1) o i).trans (by omega))
 have first:=fanout_run P U out hP
 have second:=evaluate_run p w U o out hU
 have third:=append_run p w U o out hp hpw ho
 have fourth:=clear_run P (results p w U o) U (2*w+1) (out++frame bits) (by omega) hW
 have all:=((first.seq second).seq third).seq fourth
 simpa only [machine,show ((2*U+4)+1+(8*w+11))+1+(2*w+1)+1+(4*U+9)=6*U+10*w+28 by omega] using all
end
end PCJ45bee56da9f34d5a_OffsetEmitter
