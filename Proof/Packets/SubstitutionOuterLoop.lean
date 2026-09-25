import Proof.Packets.SubstitutionOuterStep

/-! The outer reverse monomial loop of substitution. Its physical count driver
is retained, and the source cursor returns to the start of the flattened bank. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def fold (C M : Nat) (source : List Bool) (atoms : List Packet) (left stored : Packet) : Nat→Packet×Packet
  | 0=>(left,stored)
  | k+1=>
    let prior:=fold C M source atoms left stored k
    let product:=(productState C ((M-(k+1))*C) source atoms prior.1).2
    (product,VectorAccumulator.answer product prior.2)

def loopHeads (C M k : Nat) := H ((M-k)*C) 1
def loopData (C R M : Nat) (source : List Bool) (atoms : List Packet) (left stored : Packet) (k : Nat) :=
  let state:=fold C M source atoms left stored k
  A C R C state.1 (one C) (PacketVector.bank R atoms) source state.2
noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)
def budget (C R M : Nat) := M*(bodyBudget C R+3)+3

variable (C R M : Nat) (source : List Bool) (atoms : List Packet) (left stored : Packet)
variable (hlen : atoms.length=C) (hC : C+2≤R)
variable (hAtoms : ∀ P∈atoms,PacketVector.Fits R P ∧ ∀ bits∈P,bits.length=C)
variable (hguards : ∀ k,k<M→
  let state:=fold C M source atoms left stored k
  Guard C R ((M-(k+1))*C) source atoms state.1 state.2)
include hlen hC hAtoms hguards

theorem iteration (k : Nat) (hk : k<M) :
    Step body (bodyBudget C R) (loopHeads C M k) (loopData C R M source atoms left stored k)
      (loopHeads C M (k+1)) (loopData C R M source atoms left stored (k+1)) := by
  let state:=fold C M source atoms left stored k
  have h:=body_run C R ((M-(k+1))*C) source atoms state.1 state.2 hlen hC hAtoms (hguards k hk)
  have shift : (M-k)*C=(M-(k+1))*C+C := by
    have he : M-k=M-(k+1)+1 := by omega
    rw [he,Nat.add_mul,Nat.one_mul]
  simpa only [loopHeads,loopData,fold,shift] using h

theorem run :
    Step machine (budget C R M)
      (Fin.addCases (m:=43) (n:=1) (motive:=fun _=>Nat) (H (M*C) 1) (fun _=>1))
      (Fin.addCases (m:=43) (n:=1) (motive:=fun _=>List Bool)
        (A C R C left (one C) (PacketVector.bank R atoms) source stored)
        (fun _=>CompareMachine.word M))
      (Fin.addCases (m:=43) (n:=1) (motive:=fun _=>Nat) (H 0 1) (fun _=>1))
      (Fin.addCases (m:=43) (n:=1) (motive:=fun _=>List Bool)
        (A C R C (fold C M source atoms left stored M).1 (one C) (PacketVector.bank R atoms) source
          (fold C M source atoms left stored M).2)
        (fun _=>CompareMachine.word M)) := by
  have h:=PhysicalRepeatStep.run body M (bodyBudget C R) (loopHeads C M)
    (loopData C R M source atoms left stored)
    (iteration C R M source atoms left stored hlen hC hAtoms hguards)
  simpa only [machine,budget,loopHeads,loopData,fold,Nat.sub_zero,Nat.sub_self,Nat.zero_mul] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
