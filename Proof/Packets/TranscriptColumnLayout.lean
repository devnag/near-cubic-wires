import Proof.Packets.TranscriptColumnLoop

/-! Exact specialization of the physical column extractor to the ordered
row-major transcript produced by the walk loop. -/
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

theorem row_prefix_split (R : Nat) (rows : Nat → List PacketVector.Packet) (T i : Nat)
    (hi : i<T) :
    ∃ tail,PacketTranscript.prefixBank R rows T=
      PacketTranscript.prefixBank R rows i++PacketVector.bank R (rows i)++tail := by
  induction T with
  | zero=>omega
  | succ T ih=>
    by_cases he : i=T
    · subst i
      exact ⟨[],by simp only [PacketTranscript.prefix_succ,List.append_nil]⟩
    · obtain ⟨tail,ht⟩ := ih (by omega)
      refine ⟨tail++PacketVector.bank R (rows T),?_⟩
      rw [PacketTranscript.prefix_succ,ht]
      simp only [List.append_assoc]

def rowPacket (N : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N) (time : Nat) : PacketVector.Packet :=
  (rows time)[column.val]'(by rw [hlen];exact column.isLt)

def rowPrefix (R N : Nat) (rows : Nat → List PacketVector.Packet) (column : Fin N) (time : Nat) :=
  PacketTranscript.prefixBank R rows time++PacketVector.bank R ((rows time).take column.val)

theorem rowPacket_fits (R N : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N)
    (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P) (time : Nat) :
    PacketVector.Fits R (rowPacket N rows hlen column time) :=
  hfit time _ (List.getElem_mem (by rw [hlen];exact column.isLt))

theorem rowPrefix_length (R N : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N)
    (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P) (time : Nat) :
    (rowPrefix R N rows column time).length=column.val*(2*R)+time*(N*(2*R)) := by
  rw [rowPrefix,List.length_append,PacketTranscript.prefix_length R N rows hlen hfit,
    PacketVector.bank_length R _ (fun P hP=>hfit time P (List.mem_of_mem_take hP)),
    List.length_take,hlen,Nat.min_eq_left (Nat.le_of_lt column.isLt)]
  ring

theorem row_part (R N T : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N) (time : Nat) (ht : time<T) :
    ∃ post,PacketTranscript.prefixBank R rows T=
      rowPrefix R N rows column time++PacketVector.entry R (rowPacket N rows hlen column time)++post := by
  obtain ⟨tail,htail⟩ := row_prefix_split R rows T time ht
  let ix : Fin (rows time).length := ⟨column.val,by rw [hlen];exact column.isLt⟩
  refine ⟨PacketVector.bank R ((rows time).drop (column.val+1))++tail,?_⟩
  rw [htail,PacketVector.bank_split R (rows time) ix]
  simp only [rowPrefix,PacketVector.entry,rowPacket,ix,List.append_assoc]

/-- Extract one coordinate across all represented walk times. The packet
sequence is the literal list of that coordinate at times `0,...,T-1`. -/
theorem rows_run (R N T : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N) (target : List Bool)
    (old : PacketVector.Packet) (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P)
    (hold : PacketVector.Fits R old) :
    Step loop (loopBudget R N T)
      (Fin.addCases (H (column.val*(2*R)) target.length) (fun _ : Fin 1=>1))
      (Fin.addCases
        (A R N (PacketTranscript.prefixBank R rows T)
          (PacketVector.payload R old) (PacketVector.count R old) target)
        (fun _ : Fin 1=>CompareMachine.word T))
      (Fin.addCases
        (H (column.val*(2*R)+T*(N*(2*R)))
          (target++PacketVector.bank R
            (List.ofFn (fun i : Fin T=>rowPacket N rows hlen column i.val))).length)
        (fun _ : Fin 1=>1))
      (Fin.addCases
        (A R N (PacketTranscript.prefixBank R rows T)
          (PacketVector.payload R (previous (rowPacket N rows hlen column) old T))
          (PacketVector.count R (previous (rowPacket N rows hlen column) old T))
          (target++PacketVector.bank R
            (List.ofFn (fun i : Fin T=>rowPacket N rows hlen column i.val))))
        (fun _ : Fin 1=>CompareMachine.word T)) := by
  choose tail htail using (fun i : Fin T=>row_part R N T rows hlen column i.val i.isLt)
  let post := fun i=>if hi : i<T then tail ⟨i,hi⟩ else []
  apply loop_run R N T (column.val*(2*R)) (PacketTranscript.prefixBank R rows T) target
    (rowPacket N rows hlen column) old (rowPrefix R N rows column) post
    (rowPacket_fits R N rows hlen column hfit) hold
  · intro i hi
    simpa only [post,dif_pos hi] using htail ⟨i,hi⟩
  · intro i _
    exact rowPrefix_length R N rows hlen column hfit i

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
