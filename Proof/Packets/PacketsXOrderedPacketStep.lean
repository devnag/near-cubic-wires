import Proof.Packets.PacketsXCycleBoundedArithmetic
import Proof.Packets.PacketsXSubstitutionCensus

/-! Actual ordered fold steps over a resident packet bank. The fetched factor
is the left operand, exactly as in the frozen right folds. Every physical
resource guard follows from the finite code bound and packet census. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

noncomputable def multiply := TapeEmbedding.machine 3
  (ReusableArithmetic.machine NormalizedMultiply.machine)
noncomputable def add := TapeEmbedding.machine 3
  (ReusableArithmetic.machine NormalizedAddition.machine)
noncomputable def addMachine := Composition.machine ArithmeticLookup.machine add

def bank (C R : Nat) (ps : List (Ring.Poly Nat)) :=
  PacketVector.bank R (ps.map (List.map (maskNat C)))
def A (C R index : Nat) (left acc : Ring.Poly Nat) (ps : List (Ring.Poly Nat)) :=
  ArithmeticLookup.A C R index (left.map (maskNat C)) (acc.map (maskNat C)) (bank C R ps)
def budget (C w index : Nat) :=
  ArithmeticLookup.budget (commonReserve C w) index+1+ReusableArithmetic.boundedBudget C w

theorem bank_fit (C w : Nat) (ps : List (Ring.Poly Nat))
    (hps : ∀P∈ps,P.length≤2^w) :
    ∀Q∈ps.map (List.map (maskNat C)),PacketVector.Fits (commonReserve C w) Q := by
  intro Q hQ
  obtain ⟨P,hP,rfl⟩:=List.mem_map.mp hQ
  exact (SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C P)
    (by simpa only [List.length_map] using hps P hP)).1

theorem fetch (C w : Nat) (ps : List (Ring.Poly Nat)) (i : Fin ps.length)
    (left acc : Ring.Poly Nat) (hl : left.length≤2^w) (hps : ∀P∈ps,P.length≤2^w) :
    Step ArithmeticLookup.machine (ArithmeticLookup.budget (commonReserve C w) i.val)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) i.val left acc ps)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) i.val ps[i.val] acc ps) := by
  let masks:=ps.map (List.map (maskNat C))
  let ix : Fin masks.length:=⟨i.val,by simpa only [masks,List.length_map] using i.isLt⟩
  have hfit:=bank_fit C w ps hps
  have leftfit:=(SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C left)
    (by simpa only [List.length_map] using hl)).1
  have selectedfit:=hfit masks[ix.val] (List.getElem_mem ix.isLt)
  have hpre : (PacketVector.bank (commonReserve C w) (masks.take ix.val)).length=
      2*ix.val*commonReserve C w := by
    rw [PacketVector.bank_length _ _ (fun P hP=>hfit P (List.mem_of_mem_take hP)),List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt ix.isLt)]
  have run:=ArithmeticLookup.run C (commonReserve C w) ix.val
    (left.map (maskNat C)) (acc.map (maskNat C)) masks[ix.val]
    (PacketVector.bank (commonReserve C w) (masks.take ix.val))
    (PacketVector.bank (commonReserve C w) (masks.drop (ix.val+1))) hpre leftfit.1
    (by simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using leftfit.2)
    selectedfit.1
    (by simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using selectedfit.2)
  dsimp only at run
  change Step _ _ _ (ArithmeticLookup.A _ _ _ _ _
    (PacketVector.bank _ (masks.take ix.val)++PacketVector.payload _ masks[ix.val]++
      PacketVector.count _ masks[ix.val]++PacketVector.bank _ (masks.drop (ix.val+1)))) _
    (ArithmeticLookup.A _ _ _ _ _
    (PacketVector.bank _ (masks.take ix.val)++PacketVector.payload _ masks[ix.val]++
      PacketVector.count _ masks[ix.val]++PacketVector.bank _ (masks.drop (ix.val+1)))) at run
  rw [←PacketVector.bank_split _ masks ix] at run
  simpa only [A,bank,masks,ix,List.getElem_map] using run

theorem embed_heads : Fin.addCases (m:=34) (n:=3) (motive:=fun _=>Nat)
    ReusableArithmetic.heads (![0,1,0] : Fin 3→Nat)=ArithmeticLookup.H 0 := by
  funext i;fin_cases i <;>rfl

theorem multiply_run (C w index : Nat) (P Q : Ring.Poly Nat) (ps : List (Ring.Poly Nat))
    (hP : Fits C P) (hQ : Fits C Q) (hp : P.length≤2^w) (hq : Q.length≤2^w) (hw : 1≤w) :
    Step multiply (ReusableArithmetic.boundedBudget C w)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) index P Q ps)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) index P (Ring.mul P Q) ps) := by
  have h:=(ReusableArithmetic.nat_mul_bounded C w P Q hP hQ hp hq hw).embed
    (![0,1,0] : Fin 3→Nat)
    (![bank C (commonReserve C w) ps,ZeroPadding.pad (commonReserve C w) (CompareMachine.word index),
      List.replicate (commonReserve C w) false] : Fin 3→List Bool)
  exact (h.congr_in embed_heads rfl).congr embed_heads rfl

theorem add_run (C w index : Nat) (P Q : Ring.Poly Nat) (ps : List (Ring.Poly Nat))
    (hP : Fits C P) (hQ : Fits C Q) (normalP : Ring.Normal P) (normalQ : Ring.Normal Q)
    (hp : P.length≤2^w) (hq : Q.length≤2^w) (hw : 1≤w) :
    Step add (ReusableArithmetic.boundedBudget C w)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) index P Q ps)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) index P (Ring.add P Q) ps) := by
  have h:=(ReusableArithmetic.nat_add_bounded C w P Q hP hQ normalP normalQ hp hq hw).embed
    (![0,1,0] : Fin 3→Nat)
    (![bank C (commonReserve C w) ps,ZeroPadding.pad (commonReserve C w) (CompareMachine.word index),
      List.replicate (commonReserve C w) false] : Fin 3→List Bool)
  exact (h.congr_in embed_heads rfl).congr embed_heads rfl

theorem parity_run (C w : Nat) (ps : List (Ring.Poly Nat)) (i : Fin ps.length)
    (left acc : Ring.Poly Nat) (hl : left.length≤2^w) (hps : ∀P∈ps,P.length≤2^w)
    (hP : Fits C ps[i.val]) (hQ : Fits C acc) (normalP : Ring.Normal ps[i.val])
    (normalQ : Ring.Normal acc) (hq : acc.length≤2^w) (hw : 1≤w) :
    Step addMachine (budget C w i.val)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) i.val left acc ps)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) i.val ps[i.val] (Ring.add ps[i.val] acc) ps) := by
  exact (fetch C w ps i left acc hl hps).seq
    (add_run C w i.val ps[i.val] acc ps hP hQ normalP normalQ
      (hps _ (List.getElem_mem i.isLt)) hq hw)

theorem budget_bound (C w index : Nat) (hi : index≤commonReserve C w) :
    budget C w index≤64*(commonReserve C w+1)^2 := by
  unfold budget ArithmeticLookup.budget PacketBank.lookupBudget ReusableArithmetic.boundedBudget
  have hmul:=Nat.mul_le_mul_right (commonReserve C w) hi
  nlinarith

end PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketStep
