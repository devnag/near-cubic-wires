import Proof.Rows.FinalNativeResidueAppend

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueRestore
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots (s t : Fin 27) : Fin 3 → Fin 27 := ![s,t,23]
noncomputable def copy (s t : Fin 27) := RecoveryFocus.machine (copySlots s t)
  (MaskedReset.machine CloseoutRowsTouching.FrameStream.machine (fun _=>true))

theorem copy_run (s t : Fin 27) (hi : Function.Injective (copySlots s t))
    (F : ℕ) (bits : List Bool) (hF : 2*bits.length+1≤F+1)
    (H : Fin 27 → ℕ) (A : Fin 27 → List Bool)
    (hh : ∀ i,H (copySlots s t i)=0)
    (hsource : A s=frame bits) (htarget : A t=List.replicate F false)
    (hlog : A 23=List.replicate (F+1) false) :
    Step (copy s t) (4*bits.length+4) H A H
      (Function.update A t (ZeroPadding.pad F (frame bits))) := by
  obtain ⟨r,hr,hout,_⟩ := CloseoutRowsTouching.FrameStream.copy_run [] bits [] []
  have base : Step CloseoutRowsTouching.FrameStream.machine (2*bits.length+1)
      (![0,0] : Fin 2 → ℕ) (![frame bits,[]] : Fin 2 → List Bool)
      (![2*bits.length+1,2*bits.length+1] : Fin 2 → ℕ) (![frame bits,frame bits] : Fin 2 → List Bool) := by
    have raw := Step.of_run hr (congrArg Configuration.heads hout) (congrArg Configuration.tapes hout)
    simpa only [CloseoutRowsTouching.FrameStream.cfg,List.nil_append,List.append_nil,
      List.length_nil,Nat.zero_add,frame_length] using raw
  have padded := base.pad (![0,F] : Fin 2 → ℕ)
  have reset := padded.mask (cap:=F+1) (fun _=>true) (by intro i _; fin_cases i <;> rfl) hF
  have localRun : Step (MaskedReset.machine CloseoutRowsTouching.FrameStream.machine (fun _=>true))
      (4*bits.length+4) (fun _=>0)
      (![frame bits,List.replicate F false,List.replicate (F+1) false] : Fin 3 → List Bool)
      (fun _=>0)
      (![frame bits,ZeroPadding.pad F (frame bits),List.replicate (F+1) false] : Fin 3 → List Bool) := by
    have htime : 2*(2*bits.length+1)+2=4*bits.length+4 := by omega
    rw [htime] at reset
    refine (reset.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i; fin_cases i <;> first | exact ZeroPadding.pad_zero _ | rfl
  have hs : s≠t := fun he=>by have hx : (0 : Fin 3)=1 := hi he; cases hx
  have hl : (23 : Fin 27)≠t := fun he=>by have hx : (2 : Fin 3)=1 := hi he; cases hx
  refine (localRun.dock (copySlots s t) hi H A hh ?_).congr
    (dockH_existing (copySlots s t) H _ hh) ?_
  · intro i; fin_cases i <;> first | exact hsource | exact htarget | exact hlog
  · apply HierarchyAllocation.install_eq (copySlots s t) hi
    · intro i; fin_cases i
      · change Function.update A t _ s=frame bits
        exact (Function.update_of_ne hs _ _).trans hsource
      · change Function.update A t _ t=_
        exact Function.update_self _ _ _
      · change Function.update A t _ 23=List.replicate (F+1) false
        exact (Function.update_of_ne hl _ _).trans hlog
    · intro i hn
      exact Function.update_of_ne (fun he=>hn 1 he.symm) _ _

def workSlots (i : Fin 21) : Fin 27 := ⟨i.val+1,by omega⟩
def eraseSlots : Fin 23 → Fin 27 :=
  Fin.addCases (m:=22) (n:=1) (motive:=fun _=>Fin 27)
    (Fin.addCases (m:=21) (n:=1) (motive:=fun _=>Fin 27) workSlots (fun _=>24)) (fun _=>23)
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 21)
def blank (F : ℕ) (A : Fin 27 → List Bool) : Fin 27 → List Bool :=
  fun (i : Fin 27) => if (1 ≤ i.val ∧ i.val ≤ 21) then List.replicate F false else A i

theorem erase_run (F : ℕ) (H : Fin 27 → ℕ) (A : Fin 27 → List Bool)
    (hh : ∀ i,i≠0→i≠22→H i=0) (hlen : ∀ i,(A (workSlots i)).length≤F)
    (hd : A 24=List.replicate F true) (hl : A 23=List.replicate (F+1) false) :
    Step erase (2*F+4) H A H (blank F A) := by
  have base := Step.of_ready (RecoveryScratchErase.erase_ready F (F+1) (fun i=>A (workSlots i)) hlen)
  rw [max_self] at base
  have hz : ∀ i,H (eraseSlots i)=0 := by
    intro i; apply hh <;> fin_cases i <;> decide
  refine (base.dock eraseSlots (by decide) H A hz ?_).congr
    (dockH_existing eraseSlots H _ hz) ?_
  · intro i
    refine Fin.addCases (m:=22) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=21) (n:=1) (fun k=>?_) (fun k=>?_) j
      · simp only [eraseSlots,Fin.addCases_left]
      · simpa [eraseSlots,blank] using hd
    · simpa [eraseSlots,blank] using hl
  · apply HierarchyAllocation.install_eq eraseSlots (by decide)
    · intro i
      refine Fin.addCases (m:=22) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=21) (n:=1) (fun k=>?_) (fun k=>?_) j
        · simp only [blank,eraseSlots,Fin.addCases_left,workSlots]
          split
          · rfl
          · rename_i hn; exfalso; apply hn; constructor <;> omega
        · simpa [eraseSlots,blank] using hd
      · simpa [eraseSlots,blank] using hl
    · intro i hn
      unfold blank
      split
      · rename_i hi
        exact False.elim (hn ((⟨i.val-1,by omega⟩ : Fin 21).castAdd 1 |>.castAdd 1)
          (Fin.ext (by simp only [eraseSlots,Fin.addCases_left,workSlots]; omega)))
      · rfl

def restored (F w p : ℕ) (A : Fin 27 → List Bool) : Fin 27 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (blank F A)
    14 (ZeroPadding.pad F (frame (SignedSortKey.binary w 0))))
    15 (ZeroPadding.pad F (frame (SignedSortKey.binary w 0))))
    20 (ZeroPadding.pad F (frame (SignedSortKey.binary w 0))))
    16 (ZeroPadding.pad F (frame (SignedSortKey.binary w p)))
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine erase (copy 25 14))
    (copy 25 15)) (copy 25 20)) (copy 26 16)

theorem restore_run (F w p : ℕ) (H : Fin 27 → ℕ) (A : Fin 27 → List Bool)
    (hh : ∀ i,i≠0→i≠22→H i=0) (hlen : ∀ i,(A (workSlots i)).length≤F)
    (hd : A 24=List.replicate F true) (hl : A 23=List.replicate (F+1) false)
    (hz : A 25=frame (SignedSortKey.binary w 0))
    (hp : A 26=frame (SignedSortKey.binary w p)) (hw : 2*w≤F) :
    Step machine (2*F+16*w+24) H A H (restored F w p A) := by
  let z := ZeroPadding.pad F (frame (SignedSortKey.binary w 0))
  let A0 := blank F A
  let A1 := Function.update A0 14 z
  let A2 := Function.update A1 15 z
  let A3 := Function.update A2 20 z
  have b := erase_run F H A hh hlen hd hl
  have hbound (n : ℕ) : 2*(SignedSortKey.binary w n).length+1≤F+1 := by
    rw [SignedSortKey.binary_length]; omega
  have hhead (s t : Fin 27) (hs : s=25∨s=26) (ht : t=14∨t=15∨t=20∨t=16) :
      ∀ i,H (copySlots s t i)=0 := by
    intro i; fin_cases i
    · change H s=0
      apply hh <;> rcases hs with rfl|rfl <;> decide
    · change H t=0
      apply hh <;> rcases ht with rfl|rfl|rfl|rfl <;> decide
    · exact hh 23 (by decide) (by decide)
  have c1 := copy_run 25 14 (by decide) F (SignedSortKey.binary w 0) (hbound 0) H A0
    (hhead _ _ (Or.inl rfl) (Or.inl rfl)) (by exact hz) rfl (by exact hl)
  have c2 := copy_run 25 15 (by decide) F (SignedSortKey.binary w 0) (hbound 0) H A1
    (hhead _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)))
    (by simpa [A1,A0,blank] using hz) (by simp [A1,A0,blank]) (by simpa [A1,A0,blank] using hl)
  have c3 := copy_run 25 20 (by decide) F (SignedSortKey.binary w 0) (hbound 0) H A2
    (hhead _ _ (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))))
    (by simpa [A2,A1,A0,blank] using hz) (by simp [A2,A1,A0,blank]) (by simpa [A2,A1,A0,blank] using hl)
  have c4 := copy_run 26 16 (by decide) F (SignedSortKey.binary w p) (hbound p) H A3
    (hhead _ _ (Or.inr rfl) (Or.inr (Or.inr (Or.inr rfl))))
    (by simpa [A3,A2,A1,A0,blank] using hp) (by simp [A3,A2,A1,A0,blank]) (by simpa [A3,A2,A1,A0,blank] using hl)
  have total := (((b.seq c1).seq c2).seq c3).seq c4
  simp only [SignedSortKey.binary_length] at total
  convert total using 1 <;> first | rfl | omega

/-- The next call starts from a physically padded blank driver; its actual
width is produced by the field reader before doubling. -/
def canonical (F w p : ℕ) (source out : List Bool) : Fin 23 → List Bool := fun i=>
  if i=0 then source else if i=22 then out else
  if i=14 ∨ i=15 ∨ i=20 then ZeroPadding.pad F (frame (SignedSortKey.binary w 0)) else
  if i=16 then ZeroPadding.pad F (frame (SignedSortKey.binary w p)) else List.replicate F false

def retained (F w p : ℕ) : Fin 4 → List Bool :=
  ![List.replicate (F+1) false,List.replicate F true,
    frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w p)]

theorem restored_eq (F w p : ℕ) (source out : List Bool) (A : Fin 27 → List Bool)
    (hs : A 0=source) (ho : A 22=out)
    (hd : A 24=List.replicate F true) (hl : A 23=List.replicate (F+1) false)
    (hz : A 25=frame (SignedSortKey.binary w 0)) (hp : A 26=frame (SignedSortKey.binary w p)) :
    restored F w p A=Fin.addCases (m:=23) (n:=4) (motive:=fun _=>List Bool)
      (canonical F w p source out) (retained F w p) := by
  funext i; fin_cases i <;> simp [restored,blank,canonical,retained,Fin.addCases,hs,ho,hd,hl,hz,hp]

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueRestore
