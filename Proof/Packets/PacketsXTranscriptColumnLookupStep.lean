import Proof.Packets.PacketsXSelectedPairFetch
import Proof.Packets.PacketsXOrderedPacketReset

/-! Exact one-hot lookup step over the original contiguous coordinate bank.
The physical lookup bit may erase the fetched left operand. Addition is then
performed in both branches: adding a rejected zero must retain the original
normalized constructor's literal list order. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
abbrev Poly := Ring.Poly Nat
abbrev H := SelectedPairFetch.H
abbrev A := SelectedPairFetch.A

noncomputable def zeroLeft := PhysicalCopyPair.machine (31 : Fin 37) 36 25 36 28
noncomputable def zero := TapeEmbedding.machine 1 zeroLeft
noncomputable def filter := PhysicalBitCall.falseMachine (37 : Fin 38) zero
noncomputable def fetch := TapeEmbedding.machine 1 ArithmeticLookup.machine
noncomputable def add := TapeEmbedding.machine 1 OrderedPacketStep.add
noncomputable def machine := Composition.machine fetch (Composition.machine filter add)
def budget (C w i : Nat) := ArithmeticLookup.budget (commonReserve C w) i+1+
  ((4*commonReserve C w+8)+1+ReusableArithmetic.boundedBudget C w)

theorem zero_left_eq (C R index : Nat) (left right : Poly) (ps : List Poly) (hR : 1≤R) :
    Function.update (Function.update (OrderedPacketStep.A C R index left right ps) 25
      (List.replicate R false)) 28 (List.replicate R false)=
      OrderedPacketStep.A C R index [] right ps := by
  funext i
  fin_cases i <;>simp [OrderedPacketStep.A,ArithmeticLookup.A,Fin.addCases,
    ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,ReusableArithmetic.data,
    NormalizedMultiply.data,NormalizedMultiply.extras,OrderedPacketReset.zero_pad R hR,ZeroPadding.pad_zero]
  simp [ZeroPadding.pad]

theorem zero_left_run (C w index : Nat) (left right : Poly) (ps : List Poly)
    (hl : left.length≤2^w) :
    Step zeroLeft (4*commonReserve C w+5) (ArithmeticLookup.H 0)
      (OrderedPacketStep.A C (commonReserve C w) index left right ps) (ArithmeticLookup.H 0)
      (OrderedPacketStep.A C (commonReserve C w) index [] right ps) := by
  have hf:=(SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C left)
    (by simpa only [List.length_map] using hl)).2
  have h:=PhysicalCopyPair.run (commonReserve C w) (31 : Fin 37) 36 25 36 28
    (ArithmeticLookup.H 0) (OrderedPacketStep.A C (commonReserve C w) index left right ps)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    (by change (List.replicate (commonReserve C w) false).length=_;simp)
    (VectorAccumulator.flat_length _ _ hf)
    (by change (List.replicate (commonReserve C w) false).length=_;simp)
    (VectorAccumulator.count_length _ _ hf)
  have hR : 1≤commonReserve C w := Nat.one_le_iff_ne_zero.mpr (by unfold commonReserve;positivity)
  exact h.congr rfl (zero_left_eq C (commonReserve C w) index left right ps hR)

theorem zero_run (C w index pos : Nat) (left right : Poly) (ps : List Poly) (bits : List Bool)
    (hl : left.length≤2^w) :
    Step zero (4*commonReserve C w+5) (H pos) (A C (commonReserve C w) index left right ps bits)
      (H pos) (A C (commonReserve C w) index [] right ps bits) :=
  (zero_left_run C w index left right ps hl).embed (fun _ : Fin 1=>pos) (fun _=>bits)

theorem filter_run (C w index pos : Nat) (left right : Poly) (ps : List Poly) (bits : List Bool)
    (flag : Bool) (hb : readTapeBit bits pos=flag) (hl : left.length≤2^w) :
    Step filter (4*commonReserve C w+8) (H pos) (A C (commonReserve C w) index left right ps bits)
      (H pos) (A C (commonReserve C w) index (if flag then left else []) right ps bits) := by
  cases flag
  · exact PhysicalBitCall.false_run (37 : Fin 38) (p:=zero) hb
      (zero_run C w index pos left right ps bits hl)
  · exact (PhysicalBitCall.true_skip (p:=zero) (37 : Fin 38) (H pos)
      (A C (commonReserve C w) index left right ps bits) hb).enlarge (by omega)

theorem run (C w pos : Nat) (ps : List Poly) (j : Fin ps.length) (left acc : Poly)
    (bits : List Bool) (flag : Bool) (hb : readTapeBit bits pos=flag)
    (hl : left.length≤2^w) (hps : ∀P∈ps,P.length≤2^w)
    (hp : Fits C ps[j.val]) (hq : Fits C acc) (np : Ring.Normal ps[j.val])
    (nq : Ring.Normal acc) (hacc : acc.length≤2^w) (hw : 1≤w) :
    let chosen := if flag then ps[j.val] else []
    Step machine (budget C w j.val) (H pos) (A C (commonReserve C w) j.val left acc ps bits)
      (H pos) (A C (commonReserve C w) j.val chosen (Ring.add chosen acc) ps bits) := by
  dsimp only
  have first := SelectedPairFetch.fetch_run C w pos ps j left acc bits hl hps
  have second := filter_run C w j.val pos ps[j.val] acc ps bits flag hb (hps _ (List.getElem_mem j.isLt))
  have chosenFit : Fits C (if flag then ps[j.val] else []) := by
    cases flag
    · simp only [Bool.false_eq_true,ite_false,Fits,List.not_mem_nil,false_implies,forall_const]
    · exact hp
  have chosenNormal : Ring.Normal (if flag then ps[j.val] else []) := by
    cases flag
    · simp [Ring.Normal]
    · exact np
  have chosenLength : (if flag then ps[j.val] else []).length≤2^w := by
    cases flag
    · simp
    · exact hps _ (List.getElem_mem j.isLt)
  have third := (OrderedPacketStep.add_run C w j.val (if flag then ps[j.val] else []) acc ps
    chosenFit hq chosenNormal nq chosenLength hacc hw).embed
    (fun _ : Fin 1=>pos) (fun _=>bits)
  exact first.seq (second.seq third)

theorem budget_bound (C w i : Nat) (hi : i≤commonReserve C w) :
    budget C w i≤96*(commonReserve C w+1)^2 := by
  unfold budget ArithmeticLookup.budget PacketBank.lookupBudget ReusableArithmetic.boundedBudget
  have hm:=Nat.mul_le_mul_right (commonReserve C w) hi
  nlinarith

end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupStep
