import Proof.SourceAssembly.SourceClear

/- The paid cleanup is consumed by the actual MaskSeedCode.Ready boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourceRefill
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open PCJ6e421fabe2aa4155_SourceClear (join)
noncomputable section

def prepend {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U s : Nat}
    (c : MaskSeedCode mask packet U) (p : Machine U s) : MaskSeedCode mask packet U :=
  { c with prefixStates := _, lead := Composition.machine p c.lead }

theorem prepend_ready {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U s : Nat}
    (c : MaskSeedCode mask packet U) (p : Machine U s) (r : Request) (n fuel : Nat)
    (H₀ H H' : Fin U → Nat) (A₀ A A' : Fin U → List Bool)
    (before : Step p n H₀ A₀ H A) (rest : c.Ready r fuel H H' A A') :
    (prepend c p).Ready r (n+1+fuel) H₀ H' A₀ A' := by
  obtain ⟨mR,mH,mA,pR,pH,pA,leadFuel,suffixFuel,tailFuel,lead,suffix,tail,bound⟩ := rest
  refine ⟨mR,mH,mA,pR,pH,pA,n+1+leadFuel,suffixFuel,tailFuel,
    before.seq lead,suffix,tail,?_⟩
  omega

end
end PCJ6e421fabe2aa4155_SourceRefill
