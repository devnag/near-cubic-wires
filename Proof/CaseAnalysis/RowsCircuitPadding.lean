import Proof.CaseAnalysis.RowsCircuitAliases

/-! The same cold circuit runs in the already allocated term workspace.
Logical public streams stay unpadded; only private storage receives H cells. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPadding
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (P H : ℕ) (i : Fin 1703):=
  if i=1 then P else if i=1674 ∨ i=1688 ∨ i=1694 ∨ i=1698 ∨ i=1699 then 0 else H
def input (P H core W L : ℕ) (bits out : List Bool) (i : Fin 1703):=
  if i=1 then ZeroPadding.pad P (frame bits) else if i=1674 then UnaryTemplate.tape core
  else if i=1688 then out else if i=1694 then List.replicate P true
  else if i=1698 then List.replicate W true else if i=1699 then List.replicate L true
  else List.replicate H false

theorem padded_input (P H core W L : ℕ) (bits out : List Bool) (i : Fin 1703) :
    ZeroPadding.pad (padding P H i) (CloseoutRowsCircuitColdEntry.input P core W L bits out i)=
      input P H core W L bits out i:=by
  have eqval (a : Fin 1703) : i=a ↔ i.val=a.val:=Fin.ext_iff
  simp only [padding,input,CloseoutRowsCircuitColdEntry.input,CloseoutRowsCircuit.input,eqval]
  split_ifs <;> simp_all [ZeroPadding.pad]

theorem private_padding (P H : ℕ) (i : Fin 1703)
    (h1 : i≠1) (h2 : i≠1674) (h3 : i≠1694) (h4 : i≠1698) (h5 : i≠1699) (h6 : i≠1688) :
    padding P H i=H:=by simp only [padding,h1,h2,h3,h4,h5,h6,or_self,ite_false]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPadding
