import Proof.Packets.SubstitutionCallFinish

/-! A fully executed reusable substitution call. Its input polynomial is
resident in the right operand; the source copy and loop drivers are physically
created, all cursor motion is paid, and all nine private tapes are erased. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def prepare := Composition.machine machine (Composition.machine (moveDrivers .right) seek)
def prepareBudget (C R M : Nat) := 12*R+29+PhysicalProductSeek.budget C M
noncomputable def execute := Composition.machine prepare (Composition.machine SubstitutionOuter.machine finish)
def totalBudget (C R M : Nat) := prepareBudget C R M+1+(SubstitutionOuter.budget C R M+1+finishBudget R)

theorem prepare_run (C R : Nat) (left right : Packet) (atoms : List Bool)
    (hC : C+2≤R) (hr : VectorAccumulator.Fits R right) :
    Step prepare (prepareBudget C R right.length) heads (resident C R left right atoms)
      (loopHeads (right.length*C)) (loopTapes C R right.length left [] atoms right.flatten) := by
  have first:=run C R left right atoms hC hr
  rw [prepared_eq C R left right atoms hC] at first
  have second:=(move_drivers_run .right heads (loopTapes C R right.length left [] atoms right.flatten)).congr moved_up rfl
  have third:=seek_run C R right.length 0 left [] atoms right.flatten
  simp only [Nat.zero_add] at third
  have h:=first.seq (second.seq third)
  have hf : budget R+1+(5+1+PhysicalProductSeek.budget C right.length)=prepareBudget C R right.length := by
    unfold budget prepareBudget;omega
  rw [hf] at h
  exact h

theorem padded_loop_run (C R M : Nat) (source : List Bool) (atoms : List Packet) (left : Packet)
    (hlen : atoms.length=C) (hC : C+2≤R)
    (hAtoms : ∀ P∈atoms,PacketVector.Fits R P ∧ ∀ bits∈P,bits.length=C)
    (hguards : ∀ k,k<M→
      let state:=SubstitutionOuter.fold C M source atoms left [] k
      SubstitutionOuter.Guard C R ((M-(k+1))*C) source atoms state.1 state.2) :
    Step SubstitutionOuter.machine (SubstitutionOuter.budget C R M)
      (loopHeads (M*C)) (loopTapes C R M left [] (PacketVector.bank R atoms) source)
      (loopHeads 0)
      (loopTapes C R M (SubstitutionOuter.fold C M source atoms left [] M).1
        (SubstitutionOuter.fold C M source atoms left [] M).2 (PacketVector.bank R atoms) source) :=
  (SubstitutionOuter.run C R M source atoms left [] hlen hC hAtoms hguards).pad (loopPads R)

theorem execute_run (C R : Nat) (atoms : List Packet) (left right : Packet)
    (hlen : atoms.length=C) (hC : C+2≤R) (hr : VectorAccumulator.Fits R right)
    (hAtoms : ∀ P∈atoms,PacketVector.Fits R P ∧ ∀ bits∈P,bits.length=C)
    (hguards : ∀ k,k<right.length→
      let state:=SubstitutionOuter.fold C right.length right.flatten atoms left [] k
      SubstitutionOuter.Guard C R ((right.length-(k+1))*C) right.flatten atoms state.1 state.2)
    (hout : VectorAccumulator.Fits R (SubstitutionOuter.fold C right.length right.flatten atoms left [] right.length).2) :
    Step execute (totalBudget C R right.length) heads (resident C R left right (PacketVector.bank R atoms))
      heads (resident C R
        (SubstitutionOuter.fold C right.length right.flatten atoms left [] right.length).1
        (SubstitutionOuter.fold C right.length right.flatten atoms left [] right.length).2 (PacketVector.bank R atoms)) := by
  have first:=prepare_run C R left right (PacketVector.bank R atoms) hC hr
  have second:=padded_loop_run C R right.length right.flatten atoms left hlen hC hAtoms hguards
  have third:=finish_run C R right.length
    (SubstitutionOuter.fold C right.length right.flatten atoms left [] right.length).1
    (SubstitutionOuter.fold C right.length right.flatten atoms left [] right.length).2
    (PacketVector.bank R atoms) right.flatten hC hr.2 hr.1 hout
  exact first.seq (second.seq third)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
