import Proof.Assembly.FamilySum
import Proof.Assembly.RecordEmitter
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9856d3e73b1d4df0_.FamilyRecord
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimatorCoefficients RecoveryRootRound
open P1TopDownPaidReusable (Datum)
noncomputable section
local notation "F" => PCJ9856d3e73b1d4df0_.FamilySum.machine
local notation "E" => PCJ9856d3e73b1d4df0_.FamilySum.entry
local notation "Aft" => PCJ9856d3e73b1d4df0_.FamilySum.after
local notation "Raw" => PCJ9856d3e73b1d4df0_.FamilySum.raw
noncomputable def tapes (a : WilliamsAlgorithm) := P1TopDownPaidPayload.tapes a+1+2+4+1+11
noncomputable def inputH (a : WilliamsAlgorithm) (ds : List Datum) (S R B N : Nat) : Fin (tapes a)→Nat :=
 Fin.addCases (E a ds S R B N).heads (fun _ : Fin 11=>0)
noncomputable def inputT (a : WilliamsAlgorithm) (ds : List Datum) (S R B b v N : Nat) : Fin (tapes a)→List Bool :=
 Fin.addCases (E a ds S R B N).tapes (P1TopDownPaidFamilySum.extra b v N)
noncomputable def outputH (a : WilliamsAlgorithm) (ds : List Datum) (S R B b : Nat) (xs : List Nat) : Fin (tapes a)→Nat :=
 P1TopDownPaidFamilySum.finalHeads (Raw a) (Aft a ds S R B b xs).heads
noncomputable def outputT (a : WilliamsAlgorithm) (ds : List Datum) (S R B b v : Nat) (xs : List Nat)
 (Z : Fin 10→List Bool) : Fin (tapes a)→List Bool :=
 P1TopDownPaidFamilySum.final (Raw a) (Aft a ds S R B b xs).tapes b v xs Z

/-- The whole native family counter followed by the literal reusable record
and append consumer. Every source/metadata bank match remains explicit and is
required only at an actual family execution, not arbitrary scratch. -/
theorem run (a : WilliamsAlgorithm) (ds : List Datum) (S R B rowWidth v : Nat)
 (xs : List Nat) (total : Nat)
 (dflt : Datum)
 (hv : ∀ k (hk : k<ds.length), P1TopDownPaidReusable.Valid a B R S ds[k])
 (hwords : ds.map Datum.emit=xs.map (SignedSortKey.binary rowWidth))
 (hw : rowWidth≤v) (hx : ∀ x∈xs,x<2^rowWidth)
 (hsum : xs.sum=total) (hfit : total<2^v)
 {U : Nat} (slots : Fin (tapes a)→Fin U) (si : Function.Injective slots)
 (enc : Fin 11→Fin U) (ei : Function.Injective enc)
 (app : Fin 6→Fin U) (ai : Function.Injective app)
 (coefficient : CompetitorValidity.Estimate) (denominator D cap logSize resetSize : Nat)
 (old : List Bool) (records : List Stream.Entry)
 (H : Fin U→Nat) (A : Fin U→List Bool)
 (hH : ∀i,H (slots i)=inputH a ds S R B xs.length i)
 (hA : ∀i,A (slots i)=inputT a ds S R B rowWidth v xs.length i)
 (hc : 4*v+5≤cap) (hold : old.length≤D)
 (hl : 20*v+27≤logSize)
 (hr : CloseoutFinalC10AppendPositioning.rawBudget v records.length≤resetSize)
 (heH : ∀i,dockH slots H (outputH a ds S R B rowWidth xs) (enc i)=0)
 (haH : ∀i,dockH slots H (outputH a ds S R B rowWidth xs) (app i)=0)
 (hfields : ∀ Z,
   Step (F a) (PCJ9856d3e73b1d4df0_.FamilySum.budget a S rowWidth v xs.length)
     (inputH a ds S R B xs.length) (inputT a ds S R B rowWidth v xs.length)
     (outputH a ds S R B rowWidth xs) (outputT a ds S R B rowWidth v xs Z) →
   outputT a ds S R B rowWidth v xs Z (P1TopDownPaidFamilySum.sumSlots (Raw a) 5)=
     frame (SignedSortKey.binary v total) →
   let entry : Stream.Entry := ⟨coefficient,total,denominator⟩
   let mid := install slots A (outputT a ds S R B rowWidth v xs Z)
   (∀i,mid (enc i)=RecordEmitter.bank v entry D cap old i) ∧
   (∀i,install enc mid (RecordEmitter.bank v entry D cap
       (ZeroPadding.pad D (Stream.entryWord v entry))) (app i)=
     CloseoutFinalC10AppendPositioning.tapes v D logSize resetSize entry records i)) :
 let entry : Stream.Entry := ⟨coefficient,total,denominator⟩
 ∃ Z,
 Step (Composition.machine (RecoveryFocus.machine slots (F a))
   (Composition.machine (RecoveryFocus.machine enc RecordEmitter.machine)
     (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine)))
   (PCJ9856d3e73b1d4df0_.FamilySum.budget a S rowWidth v xs.length+1+
     (2*D+4+1+(2*RecordEmitter.emitCost v+2)+1+
       CloseoutFinalC10AppendPositioning.budget v records.length))
   H A (dockH slots H (outputH a ds S R B rowWidth xs))
   (install app
     (install enc (install slots A (outputT a ds S R B rowWidth v xs Z))
       (RecordEmitter.bank v entry D cap (ZeroPadding.pad D (Stream.entryWord v entry))))
     (CloseoutFinalC10AppendPositioning.tapes v D logSize resetSize entry (records++[entry]))) := by
 obtain ⟨Z,hcount,hvalue,_⟩ := PCJ9856d3e73b1d4df0_.FamilySum.run a ds dflt S R B rowWidth v xs
   hv hwords hw hx (by simpa only [hsum] using hfit)
 rw [hsum] at hvalue
 obtain ⟨henc,happ⟩ := hfields Z hcount hvalue
 refine ⟨Z,?_⟩
 exact (hcount.dock slots si H A hH hA).seq
   (RecordEmitter.append_run enc ei app ai v ⟨coefficient,total,denominator⟩ D cap logSize resetSize old
     records hc hold _ _ heH henc haH happ hl hr)

end
end PCJ9856d3e73b1d4df0_.FamilyRecord
