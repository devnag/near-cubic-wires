import Proof.Packets.PacketsXSelectedPairFetch

/-! A real truth-selector factor step: move to the previous assignment bit,
retreat the paired packet index, fetch the bit-selected packet, and multiply
it on the left of the resident suffix product. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SelectedFactorStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SelectedPairFetch

noncomputable def move:=RecoveryFocus.machine (fun _ : Fin 1=>(37 : Fin 38))
  (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def multiply:=TapeEmbedding.machine 1 OrderedPacketStep.multiply
noncomputable def machine:=Composition.machine move
  (Composition.machine SelectedPairFetch.retreat (Composition.machine SelectedPairFetch.machine multiply))
def budget (C w : Nat):=160*(commonReserve C w+1)^2

theorem move_run (C R index pos : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) :
    Step move 1 (H (pos+1)) (A C R index left acc ps bits)
      (H pos) (A C R index left acc ps bits) := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>pos+1) (fun _=>bits))
    (fun _ : Fin 1=>(37 : Fin 38)) (by intro i j _;exact Subsingleton.elim i j)
    (H (pos+1)) (H pos) _ _
  · intro i;rfl
  · intro i;rfl
  · intro i;simp [HeadMove.apply,H,Fin.addCases]
  · intro i;rfl
  · intro i hi
    have h37 : i≠37:=by intro he;exact hi 0 he.symm
    fin_cases i <;>simp_all [H,Fin.addCases]

theorem run (C w i : Nat) (ps : List Poly) (left acc : Poly) (bits : List Bool) (bit : Bool)
    (hb : readTapeBit bits i=bit) (hi : 2*i+1<ps.length)
    (hR : 2*i+3≤commonReserve C w) (hl : left.length≤2^w) (hps : ∀P∈ps,P.length≤2^w)
    (hp : Fits C (ps.getD (chosen i bit) [])) (ha : Fits C acc) (hc : acc.length≤2^w) (hw : 1≤w) :
    Step machine (budget C w) (H (i+1)) (A C (commonReserve C w) (2*(i+1)) left acc ps bits)
      (H i) (A C (commonReserve C w) (2*i) (ps.getD (chosen i bit) [])
        (Ring.mul (ps.getD (chosen i bit) []) acc) ps bits) := by
  have hj : chosen i bit<ps.length:=by cases bit <;>simp only [chosen,Bool.false_eq_true,ite_false,ite_true] <;>omega
  have hn : (ps.getD (chosen i bit) []).length≤2^w:=by
    rw [List.getD_eq_getElem _ _ hj]
    exact hps _ (List.getElem_mem hj)
  have one:=move_run C (commonReserve C w) (2*(i+1)) i left acc ps bits
  have two:=SelectedPairFetch.retreat_run C (commonReserve C w) (2*i+1) i left acc ps bits hR
  rw [show 2*i+1+1=2*(i+1) by omega] at two
  have three:=SelectedPairFetch.run C w i i ps left acc bits bit hb hi (by omega) hl hps
  have four:=(OrderedPacketStep.multiply_run C w (2*i) (ps.getD (chosen i bit) []) acc ps hp ha hn hc hw).embed
    (fun _ : Fin 1=>i) (fun _ : Fin 1=>bits)
  have all:=one.seq (two.seq (three.seq four))
  apply all.enlarge
  unfold budget ReusableArithmetic.boundedBudget
  nlinarith

end PCJ9eff70d512234a4c_Fixed.Materializer.SelectedFactorStep
