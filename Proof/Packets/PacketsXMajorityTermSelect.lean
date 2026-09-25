import Proof.Packets.PacketsXMajorityTermDefs

/-! Actual predicate and bit-selected product calls inside the common reusable
truth-row arena, preserving the enumerator frame and append cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

def acceptSlots : Fin 6→Fin 46:=![37,40,38,42,39,41]
noncomputable def accept:=RecoveryFocus.machine acceptSlots MajorityAccept.machine
def selectSlots (i : Fin 39) : Fin 46:=i.castAdd 7
noncomputable def select:=RecoveryFocus.machine selectSlots BooleanSelectorResident.machine

theorem accept_run (C R : Nat) (ps : List Poly) (left right : Poly) (bits : List Bool)
    (flag : Bool) (out binary : List Bool) (hb : bits.length=ps.length) (hR : 4*ps.length+5≤R) :
    Step accept (10*ps.length+21) (H out) (A C R ps left right bits 0 flag out binary)
      (H out) (A C R ps left right bits (Theorem25Completion.CycleCellBitCount.marks bits).length
        (decide ((ps.length+1)/2≤(Theorem25Completion.CycleCellBitCount.marks bits).length)) out binary) := by
  have h:=(MajorityAccept.run R bits flag (by omega)).pad (fun i : Fin 6=>if i=5 then R else 0)
  rw [hb] at h
  apply PhysicalFocusBoundary.focus h acceptSlots (by decide) (H out) (H out) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [acceptSlots,H,A,extras,MajorityAccept.A,Fin.addCases,ZeroPadding.pad_zero,hb]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [acceptSlots,H,A,extras,MajorityAccept.A,Fin.addCases,ZeroPadding.pad_zero,hb]
  · intro i away
    have h40 : i≠40:=by intro he;subst i;exact away 1 rfl
    have h41 : i≠41:=by intro he;subst i;exact away 5 rfl
    fin_cases i <;>simp_all [H,A,extras,Fin.addCases]

theorem select_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly) (left right : Poly)
    (bits : List Bool) (count : Nat) (flag : Bool) (out binary : List Bool)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hl : left.length≤2^w) (hr : right.length≤2^w) (hw : 1≤w) :
    Step select (BooleanSelectorResident.budget C w ps.length)
      (H out) (A C (commonReserve C w) ps left right bits count flag out binary)
      (H out) (A C (commonReserve C w) ps
        (OrderedPacketFold.last (factors ps bits) left ps.length)
        (Normalized.structuralGF2Product (factors ps bits)) bits count flag out binary) := by
  have h:=(BooleanSelectorResident.run C w S d ps left right bits hS hps hfit hAtom hN hl hr hw).pad
    (fun i : Fin 39=>if i=37 ∨ i=38 then commonReserve C w else 0)
  apply PhysicalFocusBoundary.focus h selectSlots (by intro i j h;exact Fin.castAdd_inj.mp h)
    (H out) (H out) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [selectSlots,A,extras,BooleanSelectorResident.A,SelectedPairFetch.A,
      Fin.addCases,ZeroPadding.pad_zero]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [selectSlots,A,extras,BooleanSelectorResident.A,SelectedPairFetch.A,
      Fin.addCases,ZeroPadding.pad_zero]
  · intro i away
    have hi : 39 ≤ i.val:=by
      by_contra hn
      let j : Fin 39:=⟨i.val,by omega⟩
      exact away j (by apply Fin.ext;rfl)
    fin_cases i <;>simp_all [H,A,extras,Fin.addCases]

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
