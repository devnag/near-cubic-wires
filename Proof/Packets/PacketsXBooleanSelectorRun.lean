import Proof.Packets.PacketsXSelectedFactorStep
import Proof.Packets.PacketsXPairedPacketMeaning

/-! An actual counted loop reads the truth assignment backwards, selects the
corresponding positive/negative packets, and realizes the exact frozen right
product. No factor bank is supplied for the assignment: the scanned bits drive
all choices on the retained paired bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.BooleanSelectorRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
open PairedPacketMeaning
noncomputable def machine:=RepeatMachine.machine SelectedFactorStep.machine (fun _ _=>true)
def budget (C w N : Nat):=N*(SelectedFactorStep.budget C w+3)+3

theorem index_fit (C w N : Nat) (hN : N≤2^w) : 2*N+1≤commonReserve C w := by
  have he : 2^w≤2^(8*w):=Nat.pow_le_pow_right (by decide) (by omega)
  have hC : 1≤(C+1)^4:=Nat.one_le_pow _ _ (by omega)
  have hp : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
  unfold commonReserve
  nlinarith

theorem run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly) (old : Poly) (bits : List Bool)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (ho : old.length≤2^w) (hw : 1≤w) :
    Step machine (budget C w ps.length)
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) (SelectedPairFetch.H ps.length) (fun _=>1))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
        (SelectedPairFetch.A C (commonReserve C w) (2*ps.length) old [[]] (ComplementPacketBank.pairs ps) bits)
        (fun _=>CompareMachine.word ps.length))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) (SelectedPairFetch.H 0) (fun _=>1))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
        (SelectedPairFetch.A C (commonReserve C w) 0
          (OrderedPacketFold.last (factors ps bits) old ps.length)
          (Normalized.structuralGF2Product (factors ps bits)) (ComplementPacketBank.pairs ps) bits)
        (fun _=>CompareMachine.word ps.length)) := by
  let fs:=factors ps bits
  have hf : fs.length=ps.length:=factors_length ps bits
  have hfb:=factors_bounded S d ps bits hps
  have hpair:=pairs_bounded S d ps hps
  have hc : ∀P∈fs,P.length≤2^w:=fun P hP=>(NormalizedIntermediate.census (hfb P hP)).trans hAtom
  let hs : Nat→Fin 38→Nat:=fun n=>SelectedPairFetch.H (ps.length-n)
  let as : Nat→Fin 38→List Bool:=fun n=>SelectedPairFetch.A C (commonReserve C w)
    (2*(ps.length-n)) (OrderedPacketFold.last fs old n) (OrderedPacketFold.value Ring.mul fs [[]] n)
    (ComplementPacketBank.pairs ps) bits
  have body : ∀n,n<ps.length→Step SelectedFactorStep.machine (SelectedFactorStep.budget C w)
      (hs n) (as n) (hs (n+1)) (as (n+1)) := by
    intro n hn
    let i:=ps.length-(n+1)
    have hi : i<ps.length:=by dsimp [i];omega
    have hv : (ComplementPacketBank.pairs ps).getD (SelectedPairFetch.chosen i (bits.getD i false)) []=
        fs.getD i []:=by rw [pair_get ps i _ hi,factors_get ps bits i hi]
    have hP:=hfb _ (List.getElem_mem (show i<fs.length by omega))
    have hPG : NormalizedIntermediate.Bounded S d (fs.getD i []):=by
      rw [List.getD_eq_getElem _ _ (show i<fs.length by omega)]
      exact hP
    have hAcc:=NormalizedIntermediate.product_prefix fs hfb n
    have run:=SelectedFactorStep.run C w i (ComplementPacketBank.pairs ps)
      (OrderedPacketFold.last fs old n) (OrderedPacketFold.value Ring.mul fs [[]] n) bits
      (bits.getD i false) rfl (by rw [pairs_length];omega)
      (by have:=index_fit C w ps.length hN;dsimp [i];omega)
      (OrderedPacketFold.last_count fs old (2^w) n ho hc)
      (fun P hP=>(NormalizedIntermediate.census (hpair P hP)).trans hAtom)
      (by rw [hv];exact SubstitutionCensus.fits_of_bounded C S hS hPG)
      (SubstitutionCensus.fits_of_bounded C S hS hAcc)
      ((NormalizedIntermediate.census hAcc).trans (by simpa only [hf] using hfit)) hw
    rw [hv] at run
    have hn' : n<fs.length:=by omega
    have hlast : OrderedPacketFold.last fs old (n+1)=fs.getD i []:=by
      simp only [OrderedPacketFold.last,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,hf,i]
    dsimp only [hs,as]
    rw [hlast,OrderedPacketFold.value_succ Ring.mul fs [[]] n hn',hf]
    simpa only [i,show ps.length-(n+1)+1=ps.length-n by omega] using run
  have result:=PhysicalRepeatStep.run SelectedFactorStep.machine ps.length
    (SelectedFactorStep.budget C w) hs as body
  dsimp only [hs,as] at result
  rw [←hf,OrderedPacketFold.value_complete] at result
  have hprod : fs.foldr Ring.mul [[]]=Normalized.structuralGF2Product fs:=by
    simpa only [NormalizedFolds.product,List.foldl_reverse,
      NearCubicWires.CanonicalFourfoldRowProgram.structuralGF2One] using NormalizedFolds.product_exact fs
  rw [hprod] at result
  simpa only [hf,Nat.sub_zero,Nat.sub_self,Nat.mul_zero,OrderedPacketFold.last,ite_true,
    OrderedPacketFold.value,List.take_zero,List.foldl_nil,machine,budget,fs,factors_length] using result

end PCJ9eff70d512234a4c_Fixed.Materializer.BooleanSelectorRun
