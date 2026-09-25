import Proof.Packets.PacketBankPrimitives

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def H (sourcePos targetPos : Nat) : Fin 5→Nat := ![1,sourcePos,targetPos,0,0]
def A (R : Nat) (source target : List Bool) : Fin 5→List Bool :=
  ![UnaryTemplate.tape R,source,target,List.replicate R false,[]]
def copySlots : Fin 3→Fin 5 := ![0,1,2]
def clearSlots : Fin 3→Fin 5 := ![0,3,1]
def sourceSlots : Fin 3→Fin 5 := ![0,1,4]
def targetSlots : Fin 3→Fin 5 := ![0,2,4]
abbrev copyMachine := RecoveryFocus.machine copySlots PhysicalBankCopy.machine
abbrev clearMachine := RecoveryFocus.machine clearSlots PhysicalBankCopy.machine
abbrev seekSource := RecoveryFocus.machine sourceSlots MaskSeek.body
abbrev seekTarget := RecoveryFocus.machine targetSlots MaskSeek.body
abbrev block := Composition.machine copyMachine
  (Composition.machine clearMachine (Composition.machine seekSource seekTarget))

theorem copy_run (R : Nat) (spre bits spost tpre old tpost : List Bool)
    (hb : bits.length=R) (ho : old.length=R) :
    Step copyMachine (2*R+2) (H spre.length tpre.length)
      (A R (spre++bits++spost) (tpre++old++tpost))
      (H spre.length tpre.length) (A R (spre++bits++spost) (tpre++bits++tpost)) := by
  have h:=PhysicalBankCopy.copy_step_boundary bits old (ho.trans hb.symm) spre spost tpre tpost
  rw [hb] at h
  exact PhysicalFocusBoundary.focus h copySlots (by decide)
    (H spre.length tpre.length) (H spre.length tpre.length)
    (A R (spre++bits++spost) (tpre++old++tpost)) (A R (spre++bits++spost) (tpre++bits++tpost))
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl))

theorem clear_run (R targetPos : Nat) (spre bits spost target : List Bool) (hb : bits.length=R) :
    Step clearMachine (2*R+2) (H spre.length targetPos) (A R (spre++bits++spost) target)
      (H spre.length targetPos) (A R (spre++List.replicate R false++spost) target) := by
  have h:=PhysicalBankCopy.copy_step_boundary (List.replicate R false) bits
    (by simpa using hb) [] [] spre spost
  simp only [List.length_replicate] at h
  refine PhysicalFocusBoundary.focus h clearSlots (by decide)
    (H spre.length targetPos) (H spre.length targetPos)
    (A R (spre++bits++spost) target) (A R (spre++List.replicate R false++spost) target)
    ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [clearSlots,A,PhysicalBankCopy.cfg]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [clearSlots,A,PhysicalBankCopy.cfg]
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl)

theorem source_run (R sourcePos targetPos : Nat) (source target : List Bool) :
    Step seekSource (2*R+2) (H sourcePos targetPos) (A R source target)
      (H (sourcePos+R) targetPos) (A R source target) := by
  obtain ⟨r,rr,rf,_⟩:=MaskSeek.row_run R sourcePos source []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h sourceSlots (by decide)
    (H sourcePos targetPos) (H (sourcePos+R) targetPos) (A R source target) (A R source target)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem target_run (R sourcePos targetPos : Nat) (source target : List Bool) :
    Step seekTarget (2*R+2) (H sourcePos targetPos) (A R source target)
      (H sourcePos (targetPos+R)) (A R source target) := by
  obtain ⟨r,rr,rf,_⟩:=MaskSeek.row_run R targetPos target []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h targetSlots (by decide)
    (H sourcePos targetPos) (H sourcePos (targetPos+R)) (A R source target) (A R source target)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem block_run (R : Nat) (spre bits spost tpre old tpost : List Bool)
    (hb : bits.length=R) (ho : old.length=R) :
    Step block (8*R+11) (H spre.length tpre.length)
      (A R (spre++bits++spost) (tpre++old++tpost))
      (H (spre.length+R) (tpre.length+R))
      (A R (spre++List.replicate R false++spost) (tpre++bits++tpost)) := by
  have first:=copy_run R spre bits spost tpre old tpost hb ho
  have second:=clear_run R tpre.length spre bits spost (tpre++bits++tpost) hb
  have third:=source_run R spre.length tpre.length
    (spre++List.replicate R false++spost) (tpre++bits++tpost)
  have fourth:=target_run R (spre.length+R) tpre.length
    (spre++List.replicate R false++spost) (tpre++bits++tpost)
  have h:=first.seq (second.seq (third.seq fourth))
  have fuel : (2*R+2)+1+((2*R+2)+1+((2*R+2)+1+(2*R+2)))=8*R+11 := by omega
  rw [fuel] at h
  exact h

abbrev packet := Composition.machine block block

theorem packet_run (R : Nat) (spre payload count spost tpre oldPayload oldCount tpost : List Bool)
    (hp : payload.length=R) (hc : count.length=R) (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step packet (16*R+23) (H spre.length tpre.length)
      (A R (spre++payload++count++spost) (tpre++oldPayload++oldCount++tpost))
      (H (spre.length+2*R) (tpre.length+2*R))
      (A R (spre++List.replicate (2*R) false++spost) (tpre++payload++count++tpost)) := by
  have first:=block_run R spre payload (count++spost) tpre oldPayload (oldCount++tpost) hp hop
  have second:=block_run R (spre++List.replicate R false) count spost
    (tpre++payload) oldCount tpost hc hoc
  simp only [List.append_assoc,List.length_append,List.length_replicate,hp] at first second
  have h:=first.seq second
  have fuel : (8*R+11)+1+(8*R+11)=16*R+23 := by omega
  rw [fuel] at h
  have zeros : List.replicate R false++List.replicate R false=List.replicate (2*R) false := by
    rw [←List.replicate_add,show R+R=2*R by omega]
  have he (n : Nat) : n+R+R=n+2*R := by omega
  simpa only [List.append_assoc,←List.append_assoc (List.replicate R false),zeros,he] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
