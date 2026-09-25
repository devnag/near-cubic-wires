import Proof.Packets.DenseAtomMaterialize
import Proof.Packets.PacketsXCycleNativeNormalizedCost
import Proof.Packets.PacketsXLiteralCache

/-! Execution guards for the actual dense atom-table pass, discharged from
its concrete constant/singleton pair shape and original numeric code bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleDenseAtomCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed.Materializer
open CloseoutRowsRawPairSeek (Pair word cacheWord)
open CycleBounds

def AtomShape (C : Nat) (p : Pair) : Prop :=
  ∃ neg bit : Bool, ∃ i : Nat, i<C ∧ p=(if neg then [[]] else [],if bit then [[i]] else [])

theorem atom_word_length (C : Nat) (p : Pair) (hp : AtomShape C p) : (word p).length≤C+8 := by
  obtain ⟨neg,bit,i,hi,rfl⟩:=hp
  cases neg <;>cases bit <;>
    simp [word,ExtIncidence.stream,ExtIncidence.monomialWord,ExtIncidence.block] <;>omega

theorem atom_facts (C : Nat) (p : Pair) (hp : AtomShape C p) :
    (p.1++p.2).length≤2 ∧ (∀m∈p.1++p.2,∀i∈m,i<C) ∧ (∀m∈p.1++p.2,m.length≤C) := by
  obtain ⟨neg,bit,i,hi,rfl⟩:=hp
  cases neg <;>cases bit <;>simp [hi] <;>omega

theorem reserve_small (C w : Nat) :
    32*(C+10)≤commonReserve C w ∧ C*(C+8)≤commonReserve C w := by
  have hp : (C+1)^2≤(C+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
  have h:=Nat.mul_le_mul hp he
  unfold commonReserve
  constructor <;>nlinarith only [h,Nat.zero_le C,Nat.zero_le (C^2)]

theorem cache_reserve (C w : Nat) (cs : List Pair) (hc : cs.length≤C)
    (hs : ∀p∈cs,AtomShape C p) : (cacheWord cs).length≤commonReserve C w := by
  have hb : (cacheWord cs).length≤cs.length*(C+8) := by
    induction cs with
    | nil=>simp [cacheWord]
    | cons p ps ih=>
      have hp:=atom_word_length C p (hs p (by simp))
      have ht:=ih (by simp only [List.length_cons] at hc;omega)
        (by intro x hx;exact hs x (by simp [hx]))
      simp only [cacheWord] at ht
      simp only [cacheWord,List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith only [hp,ht]
  exact hb.trans ((Nat.mul_le_mul_right (C+8) hc).trans (reserve_small C w).2)

theorem atom_guards (C w : Nat) (hw : 1≤w) (p : Pair) (hp : AtomShape C p) :
    CloseoutRowsRawPairCopy.budget p≤commonReserve C w+3 ∧
    (∀m∈p.1++p.2,∀i∈m,i<C) ∧
    (∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤commonReserve C w) ∧
    NativeNormalized.budget C (p.1++p.2)+3≤commonReserve C w := by
  obtain ⟨hc,hfits,hd⟩:=atom_facts C p hp
  have he : 2≤2^(2*w):=(by decide : 2≤2^1).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hc':(p.1++p.2).length≤2^(2*w):=hc.trans he
  refine ⟨?_,hfits,native_input_reserve C w _ hfits hd hc',native_budget_reserve C w _ hfits hd hc'⟩
  have h:=CloseoutRowsRawPairCopy.budget_bound p
  have hl:=atom_word_length C p hp
  have hr:=(reserve_small C w).1
  omega

theorem run (C w tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (hw : 1≤w) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,Nat.pair tag i<C)
    (hshape : ∀p∈cs,AtomShape C p)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P) :
    Step DenseAtomMaterialize.machine (DenseAtomMaterialize.budget C (commonReserve C w) cs.length)
      (DenseAtomMaterialize.H 0) (DenseAtomMaterialize.A C (commonReserve C w) tag cs initial 0)
      (DenseAtomMaterialize.H 0)
      (DenseAtomMaterialize.A C (commonReserve C w) tag cs (DenseAtomProgram.table C tag cs initial cs.length) 0) := by
  apply DenseAtomMaterialize.run C (commonReserve C w) tag cs initial
  · have h:=(reserve_small C w).1;omega
  · exact hcount
  · exact hcodes
  · exact cache_reserve C w cs hcount hshape
  · rw [DenseAtomMaterialize.codes_reflected]
    exact LiteralCacheCold.stream_reserve C w tag cs.length hcount (fun i hi=>(hcodes i hi).le)
  · exact hinit
  · exact hinits
  · intro p hp;exact (atom_guards C w hw p (hshape p hp)).1
  · intro p hp;exact (atom_guards C w hw p (hshape p hp)).2.1
  · intro p hp;exact (atom_guards C w hw p (hshape p hp)).2.2.1
  · intro p hp;exact (atom_guards C w hw p (hshape p hp)).2.2.2

end Theorem25Completion.CycleDenseAtomCost
