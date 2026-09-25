import Proof.Packets.PacketVector
import Proof.Packets.PhysicalIndexReload

/-! Store a majority result whose payload and count cursors are both zero.
The emitted packet retains literal mask/count bytes; operand cursors return
to zero so the majority reset can consume its documented final boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumnStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

def machine := Composition.machine (PhysicalIndexReload.move (3 : Fin 6) .right)
  (Composition.machine PacketBank.store (PhysicalIndexReload.move (3 : Fin 6) .left))
def budget (R : Nat) := 8*R+19

theorem run (R column : Nat) (bank : List Bool) (P : PacketVector.Packet) (hP : PacketVector.Fits R P) :
    Step machine (budget R) (PacketBank.H bank.length 0)
      (PacketBank.A R column bank (PacketVector.payload R P) (PacketVector.count R P))
      (PacketBank.H (bank++PacketVector.entry R P).length 0)
      (PacketBank.A R column (bank++PacketVector.entry R P) (PacketVector.payload R P) (PacketVector.count R P)) := by
  have first := PhysicalIndexReload.move_run (3 : Fin 6) .right (PacketBank.H bank.length 0)
    (PacketBank.A R column bank (PacketVector.payload R P) (PacketVector.count R P))
  have enter : Function.update (PacketBank.H bank.length 0) 3
      (HeadMove.right.apply (PacketBank.H bank.length 0 3))=PacketBank.H bank.length 1 := by
    funext i;fin_cases i <;> rfl
  rw [enter] at first
  have middle := PacketBank.store_run R column bank (PacketVector.payload R P) (PacketVector.count R P)
    (PacketVector.payload_length hP) (PacketVector.count_length hP)
  have after : Step PacketBank.store (PacketBank.storeBudget R) (PacketBank.H bank.length 1)
      (PacketBank.A R column bank (PacketVector.payload R P) (PacketVector.count R P))
      (PacketBank.H (bank++PacketVector.entry R P).length 1)
      (PacketBank.A R column (bank++PacketVector.entry R P) (PacketVector.payload R P) (PacketVector.count R P)) := by
    simpa only [PacketVector.entry,List.append_assoc] using middle
  have last := PhysicalIndexReload.move_run (3 : Fin 6) .left
    (PacketBank.H (bank++PacketVector.entry R P).length 1)
    (PacketBank.A R column (bank++PacketVector.entry R P) (PacketVector.payload R P) (PacketVector.count R P))
  have leave : Function.update (PacketBank.H (bank++PacketVector.entry R P).length 1) 3
      (HeadMove.left.apply (PacketBank.H (bank++PacketVector.entry R P).length 1 3))=
      PacketBank.H (bank++PacketVector.entry R P).length 0 := by
    funext i;fin_cases i <;> rfl
  rw [leave] at last
  have whole := first.seq (after.seq last)
  simpa only [machine,budget,PacketBank.storeBudget,show 1+1+((8*R+15)+1+1)=8*R+19 by omega] using whole

def paddedTapes (R column F S : Nat) (bank : List Bool) (P : PacketVector.Packet) : Fin 6 → List Bool :=
  ![ZeroPadding.pad F (UnaryTemplate.tape R),bank,ZeroPadding.pad F (PacketVector.payload R P),
    ZeroPadding.pad F (PacketVector.count R P),ZeroPadding.pad S (CompareMachine.word column),List.replicate S false]

theorem run_padded (R column F S : Nat) (bank : List Bool) (P : PacketVector.Packet) (hP : PacketVector.Fits R P) :
    Step machine (budget R) (PacketBank.H bank.length 0) (paddedTapes R column F S bank P)
      (PacketBank.H (bank++PacketVector.entry R P).length 0)
      (paddedTapes R column F S (bank++PacketVector.entry R P) P) := by
  have actual := (run R column bank P hP).pad (![F,0,F,F,S,S] : Fin 6 → Nat)
  have layout (bank : List Bool) :
      (fun i=>ZeroPadding.pad ((![F,0,F,F,S,S] : Fin 6 → Nat) i)
        (PacketBank.A R column bank (PacketVector.payload R P) (PacketVector.count R P) i))=
        paddedTapes R column F S bank P := by
    funext i;fin_cases i <;> simp [paddedTapes,PacketBank.A,ZeroPadding.pad_zero,ZeroPadding.pad]
  rw [layout,layout] at actual
  exact actual

end
end Theorem25Completion.WalkTranscriptColumnStore
