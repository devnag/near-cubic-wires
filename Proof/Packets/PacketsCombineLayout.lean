import Proof.Packets.PacketsCombineSegment
import Proof.Packets.PhysicalAppendUpdateRight

/-! # P2 kit core: the combine layout (arena + bits + inner driver + a PARKED register)

Consumer: the SYM combine's product `structuralGF2FiniteConjunction` and the THR radix row's
parity (`SymCombineStageK`/`ThrCombineStageK`, `Proof/Packets/PacketsRowPolySplitKit.lean`) both need a THIRD
polynomial register besides the arena's two (fetched `left`, accumulator `acc`): the running
product (SYM) or running parity (THR). Paper: the row's canonical polynomial expansion
(`paper.tex:1197-1200`); budget class: source-polynomial.

Layout `Fin 41` = the reused lookup-fold layout `TranscriptColumnLookupFold.A` (37-tape arena,
bits tape 37, inner driver 38) followed by the two tapes of a parked kit register (payload 39,
count 40), in the kit codec (`PacketVector.payload/count` of the support masks). Register moves
are REUSED `PhysicalCopyPair` runs; this module proves only the bank equalities they need.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-- The parked register, in the kit codec. -/
def parkWords (C R : ℕ) (P : Poly) : Fin 2 → List Bool :=
  ![ZeroPadding.pad R (P.map (maskNat C)).flatten, ZeroPadding.pad R (CompareMachine.word P.length)]

/-- The combine body layout. -/
def bodyA (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    Fin 41 → List Bool :=
  Fin.addCases (m := 39) (n := 2) (motive := fun _ => List Bool)
    (TranscriptColumnLookupFold.A C R index N left acc ps bits) (parkWords C R P)

def bodyH (pos : ℕ) : Fin 41 → ℕ :=
  Fin.addCases (m := 39) (n := 2) (motive := fun _ => ℕ) (TranscriptColumnLookupFold.H pos) (fun _ => 0)

/-! ## The arena's two registers: frame lemmas -/

theorem arena_outside_right (B R index : ℕ) (left right selected : List (List Bool))
    (source : List Bool) (i : Fin 37) (h26 : i ≠ 26) (h27 : i ≠ 27) :
    ArithmeticLookup.A B R index left right source i = ArithmeticLookup.A B R index left selected source i := by
  revert h26 h27
  refine Fin.addCases (m := 34) (n := 3) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m := 30) (n := 4) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m := 24) (n := 6) (fun l => ?_) (fun l => ?_) k
      · intro _ _
        rw [ArithmeticLookup.A_worker, ArithmeticLookup.A_worker, ArithmeticLookup.data_core,
          ArithmeticLookup.data_core]
      · intro hn26 hn27
        rw [ArithmeticLookup.A_worker, ArithmeticLookup.A_worker, ArithmeticLookup.data_extra,
          ArithmeticLookup.data_extra]
        fin_cases l
        · rfl
        · rfl
        · exact False.elim (hn26 rfl)
        · exact False.elim (hn27 rfl)
        · rfl
        · rfl
    · intro _ _
      rw [ArithmeticLookup.A_reserved, ArithmeticLookup.A_reserved]
  · intro _ _
    rw [ArithmeticLookup.A_extra, ArithmeticLookup.A_extra]


/-- Overwriting the left register with a register's two words. -/
theorem arena_set_left (B R index : ℕ) (left right Q : List (List Bool)) (source : List Bool) :
    Function.update (Function.update (ArithmeticLookup.A B R index left right source) 25
      (ZeroPadding.pad R Q.flatten)) 28 (ZeroPadding.pad R (CompareMachine.word Q.length)) =
      ArithmeticLookup.A B R index Q right source := by
  funext i
  by_cases h28 : i = 28
  · subst h28
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h28]
    by_cases h25 : i = 25
    · subst h25
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne h25]
      exact ArithmeticLookup.A_outside B R index left right Q source i h25 h28

/-- Overwriting the accumulator register with a register's two words. -/
theorem arena_set_right (B R index : ℕ) (left right Q : List (List Bool)) (source : List Bool) :
    Function.update (Function.update (ArithmeticLookup.A B R index left right source) 26
      (ZeroPadding.pad R Q.flatten)) 27 (ZeroPadding.pad R (CompareMachine.word Q.length)) =
      ArithmeticLookup.A B R index left Q source := by
  funext i
  by_cases h27 : i = 27
  · subst h27
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h27]
    by_cases h26 : i = 26
    · subst h26
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne h26]
      exact arena_outside_right B R index left right Q source i h26 h27

/-! ## Updates through the nested embedding -/

theorem update_inner (f : Fin 37 → List Bool) (b d : List Bool) (park : Fin 2 → List Bool)
    (i : Fin 37) (x : List Bool) :
    Function.update (Fin.addCases (m := 39) (n := 2) (motive := fun _ => List Bool)
      (Fin.addCases (m := 38) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 37) (n := 1) (motive := fun _ => List Bool) f (fun _ => b)) (fun _ => d)) park)
      (((i.castAdd 1).castAdd 1).castAdd 2) x =
    Fin.addCases (m := 39) (n := 2) (motive := fun _ => List Bool)
      (Fin.addCases (m := 38) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 37) (n := 1) (motive := fun _ => List Bool) (Function.update f i x)
          (fun _ => b)) (fun _ => d)) park := by
  rw [PhysicalAppendUpdate.left, PhysicalAppendUpdate.left, PhysicalAppendUpdate.left]

theorem bodyA_eq (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    bodyA C R index N left acc ps bits P =
    Fin.addCases (m := 39) (n := 2) (motive := fun _ => List Bool)
      (Fin.addCases (m := 38) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 37) (n := 1) (motive := fun _ => List Bool)
          (ArithmeticLookup.A C R index (left.map (maskNat C)) (acc.map (maskNat C))
            (OrderedPacketStep.bank C R ps)) (fun _ => bits))
        (fun _ => CompareMachine.word N)) (parkWords C R P) := rfl

theorem bodyA_26 (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    bodyA C R index N left acc ps bits P 26 = ZeroPadding.pad R (acc.map (maskNat C)).flatten := rfl
theorem bodyA_27 (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    bodyA C R index N left acc ps bits P 27 = ZeroPadding.pad R (CompareMachine.word acc.length) := by
  change ZeroPadding.pad R (CompareMachine.word (acc.map (maskNat C)).length) = _
  rw [List.length_map]
theorem bodyA_39 (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    bodyA C R index N left acc ps bits P 39 = ZeroPadding.pad R (P.map (maskNat C)).flatten := rfl
theorem bodyA_40 (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    bodyA C R index N left acc ps bits P 40 = ZeroPadding.pad R (CompareMachine.word P.length) := rfl

/-- Copy of the accumulator into the left register. -/
theorem bodyA_acc_to_left (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    Function.update (Function.update (bodyA C R index N left acc ps bits P) 25
      (bodyA C R index N left acc ps bits P 26)) 28 (bodyA C R index N left acc ps bits P 27) =
    bodyA C R index N acc acc ps bits P := by
  rw [bodyA_26, bodyA_27, bodyA_eq, bodyA_eq]
  have e25 : (25 : Fin 41) = (((25 : Fin 37).castAdd 1).castAdd 1).castAdd 2 := rfl
  have e28 : (28 : Fin 41) = (((28 : Fin 37).castAdd 1).castAdd 1).castAdd 2 := rfl
  rw [e25, update_inner, e28, update_inner]
  have hl : acc.length = (acc.map (maskNat C)).length := (List.length_map _).symm
  rw [hl, arena_set_left]

/-- Copy of the parked register into the accumulator. -/
theorem bodyA_park_to_acc (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    Function.update (Function.update (bodyA C R index N left acc ps bits P) 26
      (bodyA C R index N left acc ps bits P 39)) 27 (bodyA C R index N left acc ps bits P 40) =
    bodyA C R index N left P ps bits P := by
  rw [bodyA_39, bodyA_40, bodyA_eq, bodyA_eq]
  have e26 : (26 : Fin 41) = (((26 : Fin 37).castAdd 1).castAdd 1).castAdd 2 := rfl
  have e27 : (27 : Fin 41) = (((27 : Fin 37).castAdd 1).castAdd 1).castAdd 2 := rfl
  rw [e26, update_inner, e27, update_inner]
  have hl : P.length = (P.map (maskNat C)).length := (List.length_map _).symm
  rw [hl, arena_set_right]

theorem parkWords_set (C R : ℕ) (P Q : Poly) :
    Function.update (Function.update (parkWords C R P) 0 (ZeroPadding.pad R (Q.map (maskNat C)).flatten)) 1
      (ZeroPadding.pad R (CompareMachine.word Q.length)) = parkWords C R Q := by
  funext i
  fin_cases i
  · rfl
  · rfl

/-- Copy of the accumulator into the parked register. -/
theorem bodyA_acc_to_park (C R index N : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) :
    Function.update (Function.update (bodyA C R index N left acc ps bits P) 39
      (bodyA C R index N left acc ps bits P 26)) 40 (bodyA C R index N left acc ps bits P 27) =
    bodyA C R index N left acc ps bits acc := by
  rw [bodyA_26, bodyA_27]
  unfold bodyA
  have e39 : (39 : Fin 41) = (0 : Fin 2).natAdd 39 := rfl
  have e40 : (40 : Fin 41) = (1 : Fin 2).natAdd 39 := rfl
  rw [e39, PhysicalAppendUpdate.right, e40, PhysicalAppendUpdate.right, parkWords_set]

end
end NearCubicWires.PacketsCombine
