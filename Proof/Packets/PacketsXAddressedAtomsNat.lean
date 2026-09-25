import Proof.Packets.AddressedAtomMeaning
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXNormalizedIntermediate

/-! Exact natural-polynomial meaning and support invariant of the dense
table physically produced by the runtime code-address machine. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomsNat
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek (Pair)
open NormalizedFiniteTransport NormalizedIntermediate
open AddressedAtomProgram (index code atom index_lt atom_mem)

def answer (p : Pair) : Ring.Poly Nat := Ring.norm (p.1++p.2)
def table (coding : Nat→Nat) (cs : List Pair) (initial : List (Ring.Poly Nat)) : Nat→List (Ring.Poly Nat)
  | 0=>initial
  | j+1=>(table coding cs initial j).set (code coding cs j) (answer (atom cs j))

theorem answer_masks (C : Nat) (p : Pair) (hf : Fits C (p.1++p.2)) :
    NativeAtomStore.answer C p=(answer p).map (maskNat C) := by
  exact normalized_masks_nat C (p.1++p.2) hf

theorem table_length (coding : Nat→Nat) (cs : List Pair) (initial : List (Ring.Poly Nat)) (j : Nat) :
    (table coding cs initial j).length=initial.length := by
  induction j with
  | zero=>rfl
  | succ j ih=>simpa only [table,List.length_set] using ih

theorem table_masks (C : Nat) (coding : Nat→Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hf : ∀p∈cs,Fits C (p.1++p.2)) (j : Nat) (hj : j≤cs.length) :
    AddressedAtomProgram.table C coding cs (initial.map (List.map (maskNat C))) j=
      (table coding cs initial j).map (List.map (maskNat C)) := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [AddressedAtomProgram.table,table,ih (by omega),List.map_set]
    rw [answer_masks C (atom cs j) (hf _ (atom_mem cs j (by omega)))]

theorem table_lookup_partial (coding : Nat→Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hinj : Function.Injective coding)
    (hcodes : ∀i<cs.length,coding i< initial.length)
    (i : Nat) (hi : i<cs.length) (j : Nat) (hj : j≤cs.length) :
    (table coding cs initial j).getD (coding i) []=
      if cs.length-j≤ i then answer (cs.getD i ([],[])) else initial.getD (coding i) [] := by
  induction j with
  | zero=>simp [table,show ¬cs.length≤ i by omega]
  | succ j ih=>
    have ih':=ih (by omega)
    by_cases heq : i=index cs j
    · have hbound : code coding cs j<(table coding cs initial j).length := by
        rw [table_length]
        exact hcodes _ (index_lt cs j (by omega))
      have hle : cs.length-(j+1)≤ i := by unfold index at heq;omega
      rw [if_pos hle,heq]
      change ((table coding cs initial j).set (code coding cs j) (answer (atom cs j))).getD (code coding cs j) []=answer (atom cs j)
      simp only [List.getD_eq_getElem?_getD,List.getElem?_set_self hbound,Option.getD_some]
    · have hne : code coding cs j≠coding i := by
        intro he
        exact heq (hinj he).symm
      have hs : (table coding cs initial (j+1)).getD (coding i) []=
          (table coding cs initial j).getD (coding i) [] := by
        simp only [table,List.getD_eq_getElem?_getD,List.getElem?_set_ne hne]
      rw [hs,ih']
      have hequiv : (cs.length-(j+1)≤ i)↔(cs.length-j≤ i) := by unfold index at heq;omega
      simp only [hequiv]

theorem table_lookup (coding : Nat→Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hinj : Function.Injective coding)
    (hcodes : ∀i<cs.length,coding i< initial.length) (i : Nat) (hi : i<cs.length) :
    (table coding cs initial cs.length).getD (coding i) []=answer (cs.getD i ([],[])) := by
  simpa using table_lookup_partial coding cs initial hinj hcodes i hi cs.length le_rfl

theorem identity_lookup (cs : List Pair) (initial : List (Ring.Poly Nat))
    (hcount : cs.length ≤ initial.length) (i : Nat) (hi : i<cs.length) :
    (table id cs initial cs.length).getD i []=Ring.norm ((cs.getD i ([],[])).1++(cs.getD i ([],[])).2) := by
  exact table_lookup id cs initial (fun _ _ h=>h)
    (fun _ hj=>Nat.lt_of_lt_of_le hj hcount) i hi

theorem table_lookup_away (coding : Nat→Nat) (cs : List Pair) (initial : List (Ring.Poly Nat))
    (k : Nat) (hk : ∀i<cs.length,coding i≠k) (j : Nat) (hj : j≤cs.length) :
    (table coding cs initial j).getD k []=initial.getD k [] := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    have hne : code coding cs j≠k:=hk _ (index_lt cs j (by omega))
    simp only [table,List.getD_eq_getElem?_getD,List.getElem?_set_ne hne]
    exact ih (by omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomsNat
