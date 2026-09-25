import Proof.MachineModel.OrdinaryMatrixScoreAdvance
import Proof.MachineModel.OrdinaryMatrixScoreRightCycle

/-! A remaining assignment performs the two real increments and emits its
complete right record, returning the local cursors for the next iteration. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRightNext
open LocalBitMultitape SignedSortKey MatrixScoreLeftCycle
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine MatrixScoreAdvance.machine MatrixScoreRightCycle.machine
def budget (d p s c m : ℕ) := MatrixScoreAdvance.budget d m+1+MatrixScoreRightCycle.budget d p s c m

theorem next_run (weights right : List ℤ) (suffix : List Bool)
    (p n s c cap m id template returnCap : ℕ) (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hlen : right.length=weights.length)
    (hf : ∀ z ∈ right,z.natAbs<2^p)
    (hw : p≤ s+1) (hc : 4*(s+1)+5≤c) (hm : 2*m≤c) (hd : 2*weights.length≤c) (hcap : cap≤c+1)
    (hs : ∀ i,(work i).length≤c)
    (hrcap : returnCap≤MatrixScoreLeftRecord.budget weights.length p s c m)
    (hnext : n+1<2^weights.length) (hid : id+1<2^m)
    (hp : MatrixScoreBatch.part false right (n+1)<2^s)
    (hn : MatrixScoreBatch.part true right (n+1)<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      ∃ finalCap : ℕ,finalCap≤MatrixScoreLeftRecord.budget weights.length p s c m ∧
      ∃ actual,runFrom machine (budget weights.length p s c m)
        (RecoveryCalls.restarted machine (heads out.length)
          (tapes (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix)
            (frame (binary weights.length n)) weights.length c cap (s+1) (2^s) m id template work driver counter out returnCap))=some actual ∧
        actual.final.heads=heads (out++StablePartition.recordBits (encode s m (MatrixScoreBatch.linearForm right (n+1)) (id+1))).length ∧
        actual.final.tapes=tapes
          (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix)
          (frame (binary weights.length (n+1))) weights.length c (c+1) (s+1) (2^s) m (id+1) template finalWork
          driver counter
          (out++StablePartition.recordBits (encode s m (MatrixScoreBatch.linearForm right (n+1)) (id+1))) finalCap ∧
        actual.steps≤budget weights.length p s c m := by
  let source := MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix
  obtain ⟨advanced,ha,ah,atapes,as⟩ := MatrixScoreAdvance.advance_run source weights.length n c cap (s+1) (2^s) m id template returnCap
    work driver counter out hnext hid hd hm
  obtain ⟨finalWork,hws,finalCap,hcb,finished,hf,fh,ft,fs⟩ := MatrixScoreRightCycle.cycle_run weights right suffix
    p (n+1) s c cap m (id+1) template returnCap work driver counter out hlen hf hw hc hm hcap hs hrcap hp hn
  have hi : Composition.restart advanced.final MatrixScoreRightCycle.machine.start=
      RecoveryCalls.restarted MatrixScoreRightCycle.machine (heads out.length)
        (tapes source (frame (binary weights.length (n+1))) weights.length c cap (s+1) (2^s) m (id+1) template
          work driver counter out returnCap) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [← hi] at hf
  have joined := Composition.run_join MatrixScoreAdvance.machine MatrixScoreRightCycle.machine _ _ _ advanced finished ha hf
  refine ⟨finalWork,hws,finalCap,hcb,Composition.joinedReceipt advanced finished,joined,fh,ft,?_⟩
  change advanced.steps+1+finished.steps≤_
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreRightNext
