import Proof.Packets.DenseAtomMeaning
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXNormalizedIntermediate

/-! Exact natural-polynomial meaning and support invariant of the dense
table physically produced by the unchanged Nat.pair address machine. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomsNat
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek (Pair)
open NormalizedFiniteTransport NormalizedIntermediate
open DenseAtomProgram (index code atom index_lt atom_mem)

def answer (p : Pair) : Ring.Poly Nat := Ring.norm (p.1++p.2)
def table (tag : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat)) : Nat→List (Ring.Poly Nat)
  | 0=>initial
  | j+1=>(table tag cs initial j).set (code tag cs j) (answer (atom cs j))

theorem answer_masks (C : Nat) (p : Pair) (hf : Fits C (p.1++p.2)) :
    NativeAtomStore.answer C p=(answer p).map (maskNat C) := by
  exact normalized_masks_nat C (p.1++p.2) hf

theorem table_length (tag : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat)) (j : Nat) :
    (table tag cs initial j).length=initial.length := by
  induction j with
  | zero=>rfl
  | succ j ih=>simpa only [table,List.length_set] using ih

theorem table_masks (C tag : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hf : ∀p∈cs,Fits C (p.1++p.2)) (j : Nat) (hj : j≤cs.length) :
    DenseAtomProgram.table C tag cs (initial.map (List.map (maskNat C))) j=
      (table tag cs initial j).map (List.map (maskNat C)) := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [DenseAtomProgram.table,table,ih (by omega),List.map_set]
    rw [answer_masks C (atom cs j) (hf _ (atom_mem cs j (by omega)))]

theorem table_bounded (S : Finset Nat) (tag : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (ha : ∀p∈cs,Bounded S 1 (answer p)) (hi : ∀P∈initial,Bounded S 1 P)
    (j : Nat) (hj : j≤cs.length) : ∀P∈table tag cs initial j,Bounded S 1 P := by
  induction j with
  | zero=>exact hi
  | succ j ih=>
    intro P hP
    rcases List.mem_or_eq_of_mem_set hP with hm|rfl
    · exact ih (by omega) P hm
    · exact ha _ (atom_mem cs j (by omega))

theorem table_lookup_partial (tag : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hcodes : ∀i<cs.length,Nat.pair tag i< initial.length)
    (i : Nat) (hi : i<cs.length) (j : Nat) (hj : j≤cs.length) :
    (table tag cs initial j).getD (Nat.pair tag i) []=
      if cs.length-j≤ i then answer (cs.getD i ([],[])) else initial.getD (Nat.pair tag i) [] := by
  induction j with
  | zero=>simp [table,show ¬cs.length≤ i by omega]
  | succ j ih=>
    have ih':=ih (by omega)
    by_cases heq : i=index cs j
    · have hbound : code tag cs j<(table tag cs initial j).length := by
        rw [table_length]
        exact hcodes _ (index_lt cs j (by omega))
      have hle : cs.length-(j+1)≤ i := by unfold index at heq;omega
      rw [if_pos hle,heq]
      change ((table tag cs initial j).set (code tag cs j) (answer (atom cs j))).getD (code tag cs j) []=answer (atom cs j)
      simp only [List.getD_eq_getElem?_getD,List.getElem?_set_self hbound,Option.getD_some]
    · have hne : code tag cs j≠Nat.pair tag i := by
        intro he
        exact heq (Nat.pair_eq_pair.mp he).2.symm
      have hs : (table tag cs initial (j+1)).getD (Nat.pair tag i) []=
          (table tag cs initial j).getD (Nat.pair tag i) [] := by
        simp only [table,List.getD_eq_getElem?_getD,List.getElem?_set_ne hne]
      rw [hs,ih']
      have hequiv : (cs.length-(j+1)≤ i)↔(cs.length-j≤ i) := by unfold index at heq;omega
      simp only [hequiv]

theorem table_lookup (tag : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hcodes : ∀i<cs.length,Nat.pair tag i< initial.length) (i : Nat) (hi : i<cs.length) :
    (table tag cs initial cs.length).getD (Nat.pair tag i) []=answer (cs.getD i ([],[])) := by
  simpa using table_lookup_partial tag cs initial hcodes i hi cs.length le_rfl

theorem table_lookup_away (tag : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (k : Nat) (hk : ∀i<cs.length,Nat.pair tag i≠k) (j : Nat) (hj : j≤cs.length) :
    (table tag cs initial j).getD k []=initial.getD k [] := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    have hne : code tag cs j≠k:=hk _ (index_lt cs j (by omega))
    simp only [table,List.getD_eq_getElem?_getD,List.getElem?_set_ne hne]
    exact ih (by omega)

theorem table_lookup_other_tag (tag other : Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hne : tag≠other) (i j : Nat) (hj : j≤cs.length) :
    (table tag cs initial j).getD (Nat.pair other i) []=initial.getD (Nat.pair other i) [] := by
  exact table_lookup_away tag cs initial (Nat.pair other i)
    (fun _ _ h=>hne (Nat.pair_eq_pair.mp h).1) j hj

theorem answer_bounded (S : Finset Nat) (p : Pair)
    (hs : ∀m∈p.1++p.2,∀i∈m,i∈S) (hd : Ring.Degree 1 (p.1++p.2)) :
    Bounded S 1 (answer p) :=
  ⟨LiteralAlphabet.good_norm S (p.1++p.2) hs,Ring.degree_norm hd⟩

theorem literal_answer_bounded (S : Finset Nat) (i : Nat) (hi : i∈S) (neg bit : Bool) :
    Bounded S 1 (answer (if neg then [[]] else [],if bit then [[i]] else [])) := by
  apply answer_bounded
  · cases neg <;>cases bit <;>simp [hi]
  · cases neg <;>cases bit <;>simp [Ring.Degree]

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomsNat
