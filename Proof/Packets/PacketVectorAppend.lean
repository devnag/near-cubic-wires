import Proof.Packets.VectorBankTurnover

/-! Append an entire produced coordinate vector to a resident transcript.
The source is cleared and rewound; the destination cursor advances past the
copied vector, preserving its prefix and remaining allocated suffix. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorAppend
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open VectorTransfer
noncomputable section

def machine := Composition.machine VectorTransfer.loop
  (Composition.machine VectorTransfer.backSource VectorTransfer.backSource)
def budget (R N : Nat) := N*(20*R+36)+11

theorem rows_run (R : Nat) (rows : List VectorTransfer.Pair)
    (spre spost tpre tpost : List Bool) (hf : VectorTransfer.Fits R rows) :
    Step machine (budget R rows.length) (heads spre.length tpre.length)
      (tapes R rows.length (spre++sourceBytes rows++spost) (tpre++targetBytes rows++tpost))
      (heads spre.length (tpre.length+rows.length*(2*R)))
      (tapes R rows.length (spre++List.replicate (rows.length*(2*R)) false++spost)
        (tpre++sourceBytes rows++tpost)) := by
  let source:=spre++List.replicate (rows.length*(2*R)) false++spost
  let target:=tpre++sourceBytes rows++tpost
  have first:=VectorTransfer.loop_step R rows spre spost tpre tpost hf
  have second:=VectorTransfer.backSource_run R rows.length (spre.length+rows.length*R)
    (tpre.length+rows.length*(2*R)) source target
  have third:=VectorTransfer.backSource_run R rows.length spre.length
    (tpre.length+rows.length*(2*R)) source target
  have he : spre.length+rows.length*R+rows.length*R=spre.length+rows.length*(2*R) := by ring
  rw [he] at second
  have run:=first.seq (second.seq third)
  have fuel : (rows.length*(16*R+26)+3)+1+
      ((rows.length*(2*R+5)+3)+1+(rows.length*(2*R+5)+3))=budget R rows.length := by
    unfold budget;ring
  simpa only [machine,fuel] using run

theorem run (R : Nat) (packets : List PacketVector.Packet) (pre rest sourceTail : List Bool)
    (hR : 1 ≤ R) (hpackets : ∀P∈packets,PacketVector.Fits R P) :
    Step machine (budget R packets.length) (heads 0 pre.length)
      (tapes R packets.length (PacketVector.bank R packets++sourceTail)
        (pre++List.replicate (packets.length*(2*R)) false++rest))
      (heads 0 (pre.length+packets.length*(2*R)))
      (tapes R packets.length (List.replicate (packets.length*(2*R)) false++sourceTail)
        (pre++PacketVector.bank R packets++rest)) := by
  have empty : PacketVector.Fits R [] := by
    simpa [PacketVector.Fits,CompareMachine.word] using hR
  have zeros : ∀P∈List.replicate packets.length [],PacketVector.Fits R P := by
    intro P hP
    have he : P=[] := (List.mem_replicate.mp hP).2
    subst P;exact empty
  have he : packets.length=(List.replicate packets.length ([] : PacketVector.Packet)).length := by simp
  have h:=rows_run R (VectorBankTurnover.rows R packets (List.replicate packets.length []))
    [] sourceTail pre rest (VectorBankTurnover.rows_fits R _ _ hpackets zeros)
  simpa only [VectorBankTurnover.rows_length R _ _ he,
    VectorBankTurnover.source_bytes R _ _ he,VectorBankTurnover.target_bytes R _ _ he,
    VectorBankTurnover.zero_bank R packets.length hR,List.length_nil,List.nil_append] using h


def paddedTapes (R N S : Nat) (source target : List Bool) : Fin 6 → List Bool :=
  ![ZeroPadding.pad S (UnaryTemplate.tape R),source,target,List.replicate S false,
    List.replicate S false,ZeroPadding.pad S (CompareMachine.word N)]

theorem padded_run (R S : Nat) (packets : List PacketVector.Packet) (pre rest : List Bool)
    (hR : 1 ≤ R) (hRS : R ≤ S) (hpackets : ∀P∈packets,PacketVector.Fits R P)
    (hbank : (PacketVector.bank R packets).length ≤ S) :
    Step machine (budget R packets.length) (heads 0 pre.length)
      (paddedTapes R packets.length S (ZeroPadding.pad S (PacketVector.bank R packets))
        (pre++List.replicate (packets.length*(2*R)) false++rest))
      (heads 0 (pre.length+packets.length*(2*R)))
      (paddedTapes R packets.length S (List.replicate S false)
        (pre++PacketVector.bank R packets++rest)) := by
  let tail:=List.replicate (S-(PacketVector.bank R packets).length) false
  have base:=run R packets pre rest tail hR hpackets
  have hlen : (PacketVector.bank R packets).length=packets.length*(2*R) := by
    rw [PacketVector.bank_length R packets hpackets];ring
  have cleared : List.replicate (packets.length*(2*R)) false++tail=List.replicate S false := by
    dsimp only [tail]
    rw [←List.replicate_add,hlen]
    congr 1
    omega
  rw [cleared] at base
  have padded:=base.pad (![S,0,0,S,S,S] : Fin 6 → Nat)
  have ineq : (fun i=>ZeroPadding.pad ((![S,0,0,S,S,S] : Fin 6 → Nat) i)
      (tapes R packets.length (PacketVector.bank R packets++tail)
        (pre++List.replicate (packets.length*(2*R)) false++rest) i))=
      paddedTapes R packets.length S (ZeroPadding.pad S (PacketVector.bank R packets))
        (pre++List.replicate (packets.length*(2*R)) false++rest) := by
    funext i;fin_cases i <;>
      simp [paddedTapes,tapes,ZeroPadding.pad_zero,tail,ZeroPadding.pad,
        ←List.replicate_add,Nat.add_sub_of_le hRS]
  have outeq : (fun i=>ZeroPadding.pad ((![S,0,0,S,S,S] : Fin 6 → Nat) i)
      (tapes R packets.length (List.replicate S false) (pre++PacketVector.bank R packets++rest) i))=
      paddedTapes R packets.length S (List.replicate S false) (pre++PacketVector.bank R packets++rest) := by
    funext i;fin_cases i <;>
      simp [paddedTapes,tapes,ZeroPadding.pad_zero,ZeroPadding.pad,
        ←List.replicate_add,Nat.add_sub_of_le hRS]
  exact (padded.congr_in rfl ineq).congr rfl outeq

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorAppend
