import Proof.Packets.PacketsXOrderedPacketStep
import Proof.Packets.PhysicalCopyPair
import Proof.Packets.PhysicalOneCount

/-! Paid reset of the resident fold accumulator from the actual retained zero
backing. The one case writes its monomial count; its all-false support encodes
the empty monomial. Source bank and index remain resident. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketReset
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds OrderedPacketStep
abbrev Poly:=Ring.Poly Nat
noncomputable def zeroMachine:=PhysicalCopyPair.machine (31 : Fin 37) 36 26 36 27
noncomputable def oneMachine:=Composition.machine zeroMachine (PhysicalOneCount.into (27 : Fin 37))

theorem zero_pad (R : Nat) (hR : 1≤R) : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
  change ZeroPadding.pad R [false]=_
  simp only [ZeroPadding.pad,List.length_singleton,List.singleton_append]
  rw [←List.replicate_succ]
  congr 1
  omega

theorem zero_eq (C R index : Nat) (left right : Poly) (ps : List Poly) (hR : 1≤R) :
    Function.update (Function.update (A C R index left right ps) 26 (List.replicate R false))
      27 (List.replicate R false)=A C R index left [] ps := by
  funext i
  fin_cases i <;>simp [A,ArithmeticLookup.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
    ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,
    zero_pad R hR,ZeroPadding.pad_zero]
  simp [ZeroPadding.pad]

theorem zero_run (C w index : Nat) (left right : Poly) (ps : List Poly) (hr : right.length≤2^w) :
    Step zeroMachine (4*commonReserve C w+5) (ArithmeticLookup.H 0)
      (A C (commonReserve C w) index left right ps) (ArithmeticLookup.H 0)
      (A C (commonReserve C w) index left [] ps) := by
  have hf:=(SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C right)
    (by simpa only [List.length_map] using hr)).2
  have h:=PhysicalCopyPair.run (commonReserve C w) (31 : Fin 37) 36 26 36 27
    (ArithmeticLookup.H 0) (A C (commonReserve C w) index left right ps)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    (by change (List.replicate (commonReserve C w) false).length=_;simp)
    (VectorAccumulator.flat_length _ _ hf)
    (by change (List.replicate (commonReserve C w) false).length=_;simp)
    (VectorAccumulator.count_length _ _ hf)
  have hR : 1≤commonReserve C w:=Nat.one_le_iff_ne_zero.mpr (by unfold commonReserve;positivity)
  exact h.congr rfl (zero_eq C (commonReserve C w) index left right ps hR)

theorem one_eq (C R index : Nat) (left : Poly) (ps : List Poly) (hC : C≤R) :
    Function.update (A C R index left [] ps) 27 (ZeroPadding.pad R (CompareMachine.word 1))=
      A C R index left [[]] ps := by
  have hm : maskNat C []=List.replicate C false:=by simp [maskNat,List.ofFn_const]
  have hz : ZeroPadding.pad R (List.replicate C false)=List.replicate R false:=by
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hC]
  funext i
  fin_cases i <;>simp [A,ArithmeticLookup.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
    ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,
    hm,hz,ZeroPadding.pad_zero]
  simp [ZeroPadding.pad]

theorem one_run (C w index : Nat) (left right : Poly) (ps : List Poly) (hr : right.length≤2^w) :
    Step oneMachine (4*commonReserve C w+10) (ArithmeticLookup.H 0)
      (A C (commonReserve C w) index left right ps) (ArithmeticLookup.H 0)
      (A C (commonReserve C w) index left [[]] ps) := by
  have hR : 1≤commonReserve C w:=Nat.one_le_iff_ne_zero.mpr (by unfold commonReserve;positivity)
  have hC : C≤commonReserve C w:=by
    have hpow : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) (C+1)
    have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
    unfold commonReserve
    nlinarith
  have second:=PhysicalOneCount.into_run (commonReserve C w) (27 : Fin 37)
    (ArithmeticLookup.H 0) (A C (commonReserve C w) index left [] ps) rfl (zero_pad _ hR)
  have all:=(zero_run C w index left right ps hr).seq second
  have cost : (4*commonReserve C w+5)+1+4=4*commonReserve C w+10:=by omega
  rw [cost] at all
  exact all.congr rfl (one_eq C (commonReserve C w) index left ps hC)

end PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketReset
