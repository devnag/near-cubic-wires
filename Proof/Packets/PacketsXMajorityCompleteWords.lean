import Proof.Packets.PacketsXMajorityCompleteBootstrapReset

/-! Exact resident scalar representations at the cold majority boundary.
Existing arithmetic templates are reused with their allocated zero tails. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Theorem25Completion.CycleBounds
noncomputable section

def metadata (C R : Nat) : Fin 4→List Bool :=
  ![ZeroPadding.pad R (UnaryTemplate.tape (2*C+3)),ZeroPadding.pad R (UnaryTemplate.tape C),
    UnaryTemplate.tape R,List.replicate R true]
def palette (C R N : Nat) : Fin 10→List Bool :=
  ![metadata C R 0,metadata C R 1,metadata C R 2,metadata C R 3,
    CompareMachine.word 1,CompareMachine.word N,CompareMachine.word ((N+1)/2),
    frame (SignedSortKey.binary N 0),CompareMachine.word (2^N-1),UnaryTemplate.tape (2^N)]
def masters (C R N S : Nat) : Fin 10→List Bool := fun i=>ZeroPadding.pad S (palette C R N i)

theorem compatible (C R N S : Nat) (hR : R≤S) (hN : 2^N+2≤S) :
    Bootstrap.Compatible (palette C R N) C R N S := by
  intro i
  fin_cases i <;>simp only [palette,metadata,Palette.words,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact MatrixBucketRootPower.pad_pad R S _ hR
  · exact MatrixBucketRootPower.pad_pad R S _ hR
  · rfl
  · rfl
  · exact (Completion.SourceDock.pad_template S (2^N) hN).symm

theorem masters_compatible (C R N S : Nat) (hR : R≤S) (hN : 2^N+2≤S) :
    Bootstrap.Compatible (masters C R N S) C R N S := by
  intro i
  exact (MatrixBucketRootPower.pad_pad S S _ le_rfl).trans (compatible C R N S hR hN i)

theorem actual_compatible (C w N : Nat) (hCodes : 2^N≤2^w) :
    Bootstrap.Compatible (masters C (commonReserve C w) N ((commonReserve C w)^2))
      C (commonReserve C w) N ((commonReserve C w)^2) := by
  have room:=MajorityTermArena.count_room C w (2^N) hCodes
  have hR : 1≤commonReserve C w:=by omega
  have hs : commonReserve C w≤(commonReserve C w)^2:=by nlinarith
  exact masters_compatible C (commonReserve C w) N ((commonReserve C w)^2) hs (by omega)

theorem palette_length (C w N : Nat) (hN : N≤2^w) (hCodes : 2^N≤2^w) (hw : 1≤w) :
    ∀i,(palette C (commonReserve C w) N i).length≤(commonReserve C w)^2 := by
  have room:=MajorityTermArena.count_room C w (2^N) hCodes
  have hR : 1≤commonReserve C w:=by omega
  have hs : commonReserve C w≤(commonReserve C w)^2:=by nlinarith
  exact Bootstrap.compatible_length _ C (commonReserve C w) N ((commonReserve C w)^2)
    (palette_fits C w N hN hCodes hw)
    (compatible C (commonReserve C w) N ((commonReserve C w)^2) hs (by omega))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
