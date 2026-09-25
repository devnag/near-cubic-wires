import Proof.MachineModel.OrdinaryMatrixScoreAdvance

/-! A remaining assignment performs the two real increments and emits its
complete left record, returning the local cursors for the next iteration. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreLeftNext
open LocalBitMultitape SignedSortKey MatrixScoreLeftCycle
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine MatrixScoreAdvance.machine MatrixScoreLeftCycle.machine
def budget (d p s c m : ℕ) := MatrixScoreAdvance.budget d m+1+MatrixScoreLeftCycle.budget d p s c m

theorem next_run (weights right : List ℤ) (suffix : List Bool)
    (p n s c cap m id template returnCap : ℕ) (theta : ℤ) (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hlen : right.length=weights.length)
    (hf : ∀ z ∈ weights,z.natAbs<2^p) (htheta : theta.natAbs<2^p)
    (hw : p≤ s+1) (hc : 4*(s+1)+5≤c) (hm : 2*m≤c) (hd : 2*weights.length≤c) (hcap : cap≤c+1)
    (hs : ∀ i,(work i).length≤c) (hdr : driver.length≤c) (hctr : counter.length≤c)
    (hrcap : returnCap≤MatrixScoreLeftRecord.budget weights.length p s c m)
    (hnext : n+1<2^weights.length) (hid : id+1<2^m)
    (hp : MatrixScoreBatch.part true weights (n+1)+theta.natAbs<2^s)
    (hn : MatrixScoreBatch.part false weights (n+1)+theta.natAbs<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      ∃ finalCap : ℕ,finalCap≤MatrixScoreLeftRecord.budget weights.length p s c m ∧
      ∃ actual,runFrom machine (budget weights.length p s c m)
        (RecoveryCalls.restarted machine (heads out.length)
          (tapes (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
              frame (MatrixScoreBatch.signMagnitude p theta)++suffix)
            (frame (binary weights.length n)) weights.length c cap (s+1) (2^s) m id template work driver counter out returnCap))=some actual ∧
        actual.final.heads=heads (out++StablePartition.recordBits (encode s m (theta-MatrixScoreBatch.linearForm weights (n+1)) (id+1))).length ∧
        actual.final.tapes=tapes
          (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
            frame (MatrixScoreBatch.signMagnitude p theta)++suffix)
          (frame (binary weights.length (n+1))) weights.length c (c+1) (s+1) (2^s) m (id+1) template finalWork
          (ZeroPadding.pad c [true,true]) (zeros c)
          (out++StablePartition.recordBits (encode s m (theta-MatrixScoreBatch.linearForm weights (n+1)) (id+1))) finalCap ∧
        actual.steps≤budget weights.length p s c m := by
  let source := MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++frame (MatrixScoreBatch.signMagnitude p theta)++suffix
  obtain ⟨advanced,ha,ah,atapes,as⟩ := MatrixScoreAdvance.advance_run source weights.length n c cap (s+1) (2^s) m id template returnCap
    work driver counter out hnext hid hd hm
  obtain ⟨finalWork,hws,finalCap,hcb,finished,hf,fh,ft,fs⟩ := MatrixScoreLeftCycle.cycle_run weights right suffix
    p (n+1) s c cap m (id+1) template returnCap theta work driver counter out hlen hf htheta hw hc hm hcap hs hdr hctr hrcap hp hn
  have hi : Composition.restart advanced.final MatrixScoreLeftCycle.machine.start=
      RecoveryCalls.restarted MatrixScoreLeftCycle.machine (heads out.length)
        (tapes source (frame (binary weights.length (n+1))) weights.length c cap (s+1) (2^s) m (id+1) template
          work driver counter out returnCap) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [← hi] at hf
  have joined := Composition.run_join MatrixScoreAdvance.machine MatrixScoreLeftCycle.machine _ _ _ advanced finished ha hf
  refine ⟨finalWork,hws,finalCap,hcb,Composition.joinedReceipt advanced finished,joined,fh,ft,?_⟩
  change advanced.steps+1+finished.steps≤_
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreLeftNext
