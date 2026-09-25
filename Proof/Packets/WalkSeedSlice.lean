import Proof.Packets.WalkSeedPadding
import Proof.Packets.WalkVertexBits
import Proof.Rows.CycleHeadMove

/-! The paid Toeplitz seed splitter. Starting from the actual vertex bits and
rank template, it drops low padding and writes lower, upper and translation
bits in that order. No seed word or extra counter is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedSlice
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound Completion

def paddingSlots : Fin 2→Fin 5:=![1,0]
def lowerSlots : Fin 3→Fin 5:=![1,0,2]
def upperSlots : Fin 3→Fin 5:=![1,0,3]
def translationSlots : Fin 3→Fin 5:=![1,0,4]
def moveRank:=CycleHeadMove.machine (![.stay,.right,.stay,.stay,.stay])
noncomputable def skipPadding:=RecoveryFocus.machine paddingSlots WalkSeedPadding.machine
noncomputable def lower:=RecoveryFocus.machine lowerSlots WalkRawSegment.machine
noncomputable def upper:=RecoveryFocus.machine upperSlots WalkRawSegment.machine
noncomputable def translation:=RecoveryFocus.machine translationSlots WalkRawSegment.machine
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine moveRank skipPadding) lower) moveRank) upper) translation

def source (pad low up tr : List Bool):=pad++low++up++tr
def bank (rank : Nat) (word low up tr : List Bool) : Fin 5→List Bool:=
  ![word,UnaryTemplate.tape rank,low,up,tr]
def heads (pos driver low up tr : Nat) : Fin 5→Nat:=![pos,driver,low,up,tr]

theorem move_run (rank pos driver : Nat) (word low up tr : List Bool) :
    Step moveRank 1 (heads pos driver low.length up.length tr.length)
      (bank rank word low up tr) (heads pos (driver+1) low.length up.length tr.length)
      (bank rank word low up tr) := by
  exact (CycleHeadMove.run _ _ _).congr (by funext i;fin_cases i <;>rfl) rfl

theorem padding_run (rank : Nat) (word : List Bool) :
    Step skipPadding (2*rank+2) (heads 0 1 0 0 0) (bank rank word [] [] [])
      (heads (WalkSeedPadding.padding rank) 1 0 0 0) (bank rank word [] [] []) := by
  have base:=WalkSeedPadding.run rank 0 word
  simp only [Nat.zero_add] at base
  have h:=SourceDock.dock base paddingSlots (by decide) (heads 0 1 0 0 0) (bank rank word [] [] [])
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · funext i;fin_cases i
    · exact dockH_slot paddingSlots (by decide) _ _ 1
    · exact dockH_slot paddingSlots (by decide) _ _ 0
    all_goals exact dockH_other paddingSlots _ _ _ (by intro j;fin_cases j <;>decide)
  · funext i;fin_cases i
    · exact install_slot paddingSlots (by decide) _ _ 1
    · exact install_slot paddingSlots (by decide) _ _ 0
    all_goals exact install_other paddingSlots _ _ _ (by intro j;fin_cases j <;>decide)

theorem lower_run (rank : Nat) (pad low up tr : List Bool) (hlen : low.length=rank) :
    Step lower (2*rank+2) (heads pad.length 1 0 0 0)
      (bank rank (source pad low up tr) [] [] [])
      (heads (pad.length+rank) 1 rank 0 0) (bank rank (source pad low up tr) low [] []) := by
  have base:=WalkRawSegment.run rank low (by omega) pad (up++tr) []
  simp only [hlen,Nat.sub_self,Nat.zero_add,List.nil_append] at base
  have htime:rank+rank+2=2*rank+2:=by omega
  rw [htime] at base
  have h:=SourceDock.dock base lowerSlots (by decide) (heads pad.length 1 0 0 0)
    (bank rank (source pad low up tr) [] [] [])
    (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>simp [bank,source,lowerSlots,List.append_assoc])
  apply h.congr
  · funext i;fin_cases i
    · exact dockH_slot lowerSlots (by decide) _ _ 1
    · exact dockH_slot lowerSlots (by decide) _ _ 0
    · exact dockH_slot lowerSlots (by decide) _ _ 2
    all_goals exact dockH_other lowerSlots _ _ _ (by intro j;fin_cases j <;>decide)
  · funext i;fin_cases i
    · simpa [bank,source,lowerSlots,List.append_assoc] using install_slot lowerSlots (by decide)
        (bank rank (source pad low up tr) [] [] []) (![UnaryTemplate.tape rank,pad++low++(up++tr),low]) 1
    · exact install_slot lowerSlots (by decide) _ _ 0
    · exact install_slot lowerSlots (by decide) _ _ 2
    all_goals exact install_other lowerSlots _ _ _ (by intro j;fin_cases j <;>decide)

theorem upper_run (rank : Nat) (hr : 0<rank) (pad low up tr : List Bool)
    (hl : low.length=rank) (hu : up.length=rank-1) :
    Step upper (2*rank+1) (heads (pad.length+rank) 2 rank 0 0)
      (bank rank (source pad low up tr) low [] [])
      (heads (pad.length+rank+(rank-1)) 1 rank (rank-1) 0)
      (bank rank (source pad low up tr) low up []) := by
  have base:=WalkRawSegment.run rank up (by omega) (pad++low) tr []
  have hd:rank-up.length+1=2:=by omega
  have ht:up.length+rank+2=2*rank+1:=by omega
  simp only [hd,ht,List.length_append,hl,List.nil_append] at base
  have h:=SourceDock.dock base upperSlots (by decide) (heads (pad.length+rank) 2 rank 0 0)
    (bank rank (source pad low up tr) low [] [])
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · funext i;fin_cases i
    · simpa [heads,upperSlots,hu] using dockH_slot upperSlots (by decide)
        (heads (pad.length+rank) 2 rank 0 0) (![1,pad.length+rank+up.length,up.length]) 1
    · exact dockH_slot upperSlots (by decide) _ _ 0
    · exact dockH_other upperSlots _ _ _ (by intro j;fin_cases j <;>decide)
    · simpa [heads,upperSlots,hu] using dockH_slot upperSlots (by decide)
        (heads (pad.length+rank) 2 rank 0 0) (![1,pad.length+rank+up.length,up.length]) 2
    · exact dockH_other upperSlots _ _ _ (by intro j;fin_cases j <;>decide)
  · funext i;fin_cases i
    · exact install_slot upperSlots (by decide) _ _ 1
    · exact install_slot upperSlots (by decide) _ _ 0
    · exact install_other upperSlots _ _ _ (by intro j;fin_cases j <;>decide)
    · exact install_slot upperSlots (by decide) _ _ 2
    · exact install_other upperSlots _ _ _ (by intro j;fin_cases j <;>decide)

theorem translation_run (rank : Nat) (pad low up tr : List Bool)
    (hl : low.length=rank) (hu : up.length=rank-1) (ht : tr.length=rank) :
    Step translation (2*rank+2) (heads (pad.length+rank+(rank-1)) 1 rank (rank-1) 0)
      (bank rank (source pad low up tr) low up [])
      (heads (source pad low up tr).length 1 rank (rank-1) rank)
      (bank rank (source pad low up tr) low up tr) := by
  have base:=WalkRawSegment.run rank tr (by omega) (pad++low++up) [] []
  have htime:rank+rank+2=2*rank+2:=by omega
  simp only [ht,Nat.sub_self,Nat.zero_add,List.length_append,hl,hu,List.nil_append,List.append_nil,htime] at base
  have h:=SourceDock.dock base translationSlots (by decide)
    (heads (pad.length+rank+(rank-1)) 1 rank (rank-1) 0)
    (bank rank (source pad low up tr) low up [])
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · funext i;fin_cases i
    · simpa [heads,translationSlots,source,List.length_append,hl,hu,ht,Nat.add_assoc] using
        dockH_slot translationSlots (by decide) (heads (pad.length+rank+(rank-1)) 1 rank (rank-1) 0)
          (![1,pad.length+rank+(rank-1)+rank,rank]) 1
    · exact dockH_slot translationSlots (by decide) _ _ 0
    · exact dockH_other translationSlots _ _ _ (by intro j;fin_cases j <;>decide)
    · exact dockH_other translationSlots _ _ _ (by intro j;fin_cases j <;>decide)
    · exact dockH_slot translationSlots (by decide) _ _ 2
  · funext i;fin_cases i
    · exact install_slot translationSlots (by decide) _ _ 1
    · exact install_slot translationSlots (by decide) _ _ 0
    · exact install_other translationSlots _ _ _ (by intro j;fin_cases j <;>decide)
    · exact install_other translationSlots _ _ _ (by intro j;fin_cases j <;>decide)
    · exact install_slot translationSlots (by decide) _ _ 2

theorem run (rank : Nat) (hr : 0<rank) (pad low up tr : List Bool)
    (hp : pad.length=WalkSeedPadding.padding rank) (hl : low.length=rank)
    (hu : up.length=rank-1) (ht : tr.length=rank) :
    Step machine (8*rank+14) (fun _=>0) (bank rank (source pad low up tr) [] [] [])
      (heads (source pad low up tr).length 1 rank (rank-1) rank)
      (bank rank (source pad low up tr) low up tr) := by
  have h0:=move_run rank 0 0 (source pad low up tr) [] [] []
  have h1:=padding_run rank (source pad low up tr)
  rw [←hp] at h1
  have h2:=lower_run rank pad low up tr hl
  have h3:=move_run rank (pad.length+rank) 1 (source pad low up tr) low [] []
  simp only [hl,List.length_nil] at h3
  have h4:=upper_run rank hr pad low up tr hl hu
  have h5:=translation_run rank pad low up tr hl hu ht
  have h:=((((h0.seq h1).seq h2).seq h3).seq h4).seq h5
  have htime:((((1+1+(2*rank+2))+1+(2*rank+2))+1+1)+1+(2*rank+1))+1+(2*rank+2)=8*rank+14:=by omega
  rw [htime] at h
  exact h.congr_in (by funext i;fin_cases i <;>rfl) rfl

end Theorem25Completion.WalkSeedSlice
