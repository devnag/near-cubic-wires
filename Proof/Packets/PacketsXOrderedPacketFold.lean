import Proof.Packets.PacketsXOrderedPacketStep
import Proof.Packets.PhysicalIndexedExists

/-! Descending physical indexed loops for exact ordered normalized products
and parities. The index changes on tape before each fetch; a separate retained
count drives the finite loop. All arithmetic guards are derived from census. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
open OrderedPacketStep

abbrev Poly := Ring.Poly Nat

def value (op : Poly→Poly→Poly) (ps : List Poly) (initial : Poly) (n : Nat) :=
  (ps.reverse.take n).foldl (fun acc P=>op P acc) initial

def last (ps : List Poly) (old : Poly) (n : Nat) :=
  if n=0 then old else ps.getD (ps.length-n) []

def H : Fin 38→Nat := Fin.addCases (m:=37) (n:=1) (motive:=fun _=>Nat)
  (ArithmeticLookup.H 0) (fun _=>1)
def tapes (C R index N : Nat) (left acc : Poly) (ps : List Poly) : Fin 38→List Bool :=
  Fin.addCases (m:=37) (n:=1) (motive:=fun _=>List Bool) (A C R index left acc ps)
    (fun _=>ZeroPadding.pad R (CompareMachine.word N))
def budget (C w N : Nat) := N*(64*(commonReserve C w+1)^2+2*N+6)+3
noncomputable def addMachine := PhysicalIndexedAt.downMachine (35 : Fin 37) OrderedPacketStep.addMachine

theorem value_succ (op : Poly→Poly→Poly) (ps : List Poly) (initial : Poly) (n : Nat)
    (hn : n<ps.length) :
    value op ps initial (n+1)=op (ps.getD (ps.length-(n+1)) []) (value op ps initial n) := by
  have hr : n<ps.reverse.length := by simpa only [List.length_reverse] using hn
  have hj : ps.length-(n+1)<ps.length := by omega
  unfold value
  rw [List.take_succ_eq_append_getElem hr,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,List.getElem_reverse]
  rw [List.getD_eq_getElem _ _ hj]
  simp only [Nat.sub_sub,Nat.add_comm 1 n]

theorem value_complete (op : Poly→Poly→Poly) (ps : List Poly) (initial : Poly) :
    value op ps initial ps.length=ps.foldr op initial := by
  unfold value
  rw [List.take_of_length_le (by simp),List.foldl_reverse]

theorem last_count (ps : List Poly) (old : Poly) (T n : Nat)
    (ho : old.length≤T) (hps : ∀P∈ps,P.length≤T) : (last ps old n).length≤T := by
  unfold last
  split
  · exact ho
  · by_cases hn : ps.length-n<ps.length
    · rw [List.getD_eq_getElem _ _ hn]
      exact hps _ (List.getElem_mem hn)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp

theorem update_index (C R i j : Nat) (left acc : Poly) (ps : List Poly) :
    Function.update (A C R i left acc ps) (35 : Fin 37) (ZeroPadding.pad R (CompareMachine.word j))=
      A C R j left acc ps := by
  funext k
  fin_cases k <;>simp [A,ArithmeticLookup.A,Fin.addCases]

theorem driver_fit (C w N : Nat) (hN : N≤2^w) : N+1≤commonReserve C w := by
  have he : 2^w≤2^(8*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hC : 1≤(C+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hp : 1≤2^(8*w) := Nat.one_le_pow _ _ (by decide)
  unfold commonReserve
  nlinarith

/-- Internal generic loop lemma. Both public instances below supply the actual
checked arithmetic machine and derive its step from finite mathematical data. -/
theorem loop {s : Nat} (worker : Machine 37 s) (op : Poly→Poly→Poly)
    (C w : Nat) (ps : List Poly) (old initial : Poly) (hN : ps.length≤2^w)
    (execute : ∀n,n<ps.length→
      Step worker (64*(commonReserve C w+1)^2) (ArithmeticLookup.H 0)
        (A C (commonReserve C w) (ps.length-(n+1)) (last ps old n) (value op ps initial n) ps)
        (ArithmeticLookup.H 0)
        (A C (commonReserve C w) (ps.length-(n+1)) (ps.getD (ps.length-(n+1)) [])
          (op (ps.getD (ps.length-(n+1)) []) (value op ps initial n)) ps)) :
    Step (PhysicalIndexedAt.downMachine (35 : Fin 37) worker) (budget C w ps.length)
      H (tapes C (commonReserve C w) ps.length ps.length old initial ps)
      H (tapes C (commonReserve C w) 0 ps.length (last ps old ps.length) (ps.foldr op initial) ps) := by
  let P : Nat→(Fin 37→List Bool)→Prop:=fun n a=>
    a=A C (commonReserve C w) (ps.length-n) (last ps old n) (value op ps initial n) ps
  have entry : P 0 (A C (commonReserve C w) ps.length old initial ps) := by
    simp only [P,last,value,Nat.sub_zero,ite_true,List.take_zero,List.foldl_nil]
  have idx : ∀n,n≤ps.length→∀a,P n a→a 35=
      ZeroPadding.pad (commonReserve C w) (CompareMachine.word (ps.length-n)) := by
    intro n _ a ha
    rw [ha]
    rfl
  have step : ∀n,n<ps.length→∀a,P n a→∃b,
      Step worker (64*(commonReserve C w+1)^2) (ArithmeticLookup.H 0)
        (Function.update a 35 (ZeroPadding.pad (commonReserve C w) (CompareMachine.word (ps.length-(n+1)))))
        (ArithmeticLookup.H 0) b ∧ P (n+1) b := by
    intro n hn a ha
    rw [ha,update_index]
    refine ⟨_,execute n hn,?_⟩
    dsimp only [P]
    rw [value_succ op ps initial n hn]
    simp only [last,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
  obtain ⟨B,hB,hP,_⟩:=PhysicalIndexedExists.run_down_padded (35 : Fin 37) worker ps.length
    (64*(commonReserve C w+1)^2) (commonReserve C w) (ArithmeticLookup.H 0) rfl
    (driver_fit C w ps.length hN) P _ entry idx step
  rw [hP] at hB
  simpa only [Nat.sub_self,value_complete,H,tapes,budget] using hB

theorem parity_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly) (old : Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^d≤2^w) (hN : ps.length≤2^w) (ho : old.length≤2^w) (hw : 1≤w) :
    Step addMachine (budget C w ps.length)
      H (tapes C (commonReserve C w) ps.length ps.length old [] ps)
      H (tapes C (commonReserve C w) 0 ps.length (last ps old ps.length)
        (ps.foldr Ring.add []) ps) := by
  apply loop OrderedPacketStep.addMachine Ring.add C w ps old [] hN
  intro n hn
  have hj : ps.length-(n+1)<ps.length := by omega
  let i : Fin ps.length:=⟨ps.length-(n+1),hj⟩
  have hc : ∀P∈ps,P.length≤2^w:=fun P hP=>(NormalizedIntermediate.census (hps P hP)).trans hfit
  have hp:=hps ps[i.val] (List.getElem_mem i.isLt)
  have hacc:=NormalizedIntermediate.parity_prefix ps hps n
  have run:=OrderedPacketStep.parity_run C w ps i (last ps old n) (value Ring.add ps [] n)
    (last_count ps old (2^w) n ho hc) hc
    (SubstitutionCensus.fits_of_bounded C S hS hp)
    (SubstitutionCensus.fits_of_bounded C S hS hacc) hp.1.1 hacc.1.1
    ((NormalizedIntermediate.census hacc).trans hfit) hw
  have cap : i.val≤commonReserve C w := by have:=driver_fit C w ps.length hN;omega
  have enlarged:=run.enlarge (OrderedPacketStep.budget_bound C w i.val cap)
  simpa only [i,List.getD_eq_getElem _ _ hj] using enlarged

end PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketFold
