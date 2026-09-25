import Proof.Packets.TranscriptColumnBody
import Proof.Packets.PacketTranscript
import Proof.Packets.PhysicalRepeatStep

/-! A counted physical extraction of a time column. The source decompositions
are byte equalities; the proof supplies every actual machine execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def columnPrefix (R : Nat) (packets : Nat → PacketVector.Packet) (k : Nat) :=
  PacketTranscript.prefixBank R (fun i=>[packets i]) k

theorem prefix_zero (R : Nat) (packets : Nat → PacketVector.Packet) :
    columnPrefix R packets 0=[] := rfl

def previous (packets : Nat → PacketVector.Packet) (old : PacketVector.Packet) (k : Nat) :=
  if k=0 then old else packets (k-1)

theorem previous_zero (packets : Nat → PacketVector.Packet) (old : PacketVector.Packet) :
    previous packets old 0=old := by simp [previous]

theorem previous_succ (packets : Nat → PacketVector.Packet) (old : PacketVector.Packet) (k : Nat) :
    previous packets old (k+1)=packets k := by simp [previous]

theorem prefix_succ (R : Nat) (packets : Nat → PacketVector.Packet) (k : Nat) :
    columnPrefix R packets (k+1)=columnPrefix R packets k++PacketVector.entry R (packets k) := by
  simp only [columnPrefix,PacketTranscript.prefix_succ,PacketVector.bank,List.flatMap_singleton]

theorem prefix_ofFn (R : Nat) (packets : Nat → PacketVector.Packet) (k : Nat) :
    columnPrefix R packets k=PacketVector.bank R (List.ofFn (fun i : Fin k=>packets i.val)) := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [prefix_succ,List.ofFn_succ_last,PacketVector.bank_append]
    simpa only [Fin.val_castSucc,Fin.val_last,PacketVector.bank,List.flatMap_singleton] using
      congrArg (fun word=>word++PacketVector.entry R (packets k)) ih

def loop := RepeatMachine.machine body (fun _ _=>true)
def loopBudget (R N T : Nat) := T*(bodyBudget R N+3)+3

/-- Every visit copies the represented packet at offset `offset+i*(N*2R)`.
The resulting bank is in increasing visit order, with no permutation or
normalization of any polynomial packet. -/
theorem loop_run (R N T offset : Nat) (source target : List Bool)
    (packets : Nat → PacketVector.Packet) (old : PacketVector.Packet)
    (pre post : Nat → List Bool)
    (hfit : ∀i,PacketVector.Fits R (packets i)) (hold : PacketVector.Fits R old)
    (hsource : ∀i,i<T→source=pre i++PacketVector.entry R (packets i)++post i)
    (hposition : ∀i,i<T→(pre i).length=offset+i*(N*(2*R))) :
    Step loop (loopBudget R N T)
      (Fin.addCases (H offset target.length) (fun _ : Fin 1=>1))
      (Fin.addCases (A R N source (PacketVector.payload R old) (PacketVector.count R old) target)
        (fun _ : Fin 1=>CompareMachine.word T))
      (Fin.addCases
        (H (offset+T*(N*(2*R)))
          (target++PacketVector.bank R (List.ofFn (fun i : Fin T=>packets i.val))).length)
        (fun _ : Fin 1=>1))
      (Fin.addCases
        (A R N source (PacketVector.payload R (previous packets old T))
          (PacketVector.count R (previous packets old T))
          (target++PacketVector.bank R (List.ofFn (fun i : Fin T=>packets i.val))))
        (fun _ : Fin 1=>CompareMachine.word T)) := by
  let hs := fun k=>H (offset+k*(N*(2*R))) (target++columnPrefix R packets k).length
  let tapes := fun k=>A R N source (PacketVector.payload R (previous packets old k))
    (PacketVector.count R (previous packets old k)) (target++columnPrefix R packets k)
  have hpast (i : Nat) : PacketVector.Fits R (previous packets old i) := by
    unfold previous
    split_ifs
    · exact hold
    · exact hfit _
  have localStep (i : Nat) (hi : i<T) :
      Step body (bodyBudget R N) (hs i) (tapes i) (hs (i+1)) (tapes (i+1)) := by
    have step := body_run R N (pre i) (post i) (target++columnPrefix R packets i)
      (packets i) (previous packets old i) (hfit i) (hpast i)
    rw [←hsource i hi,hposition i hi] at step
    have pos : offset+i*(N*(2*R))+N*(2*R)=offset+(i+1)*(N*(2*R)) := by ring
    simpa only [hs,tapes,prefix_succ,previous_succ,pos,List.append_assoc] using step
  have result := PhysicalRepeatStep.run body T (bodyBudget R N) hs tapes localStep
  dsimp only [hs,tapes] at result
  rw [prefix_zero] at result
  simpa only [loop,loopBudget,Nat.zero_mul,Nat.add_zero,previous_zero,
    List.append_nil,prefix_ofFn] using result

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
