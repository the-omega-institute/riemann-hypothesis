import AlpogePureZetaWindowExtraction
import Verification.AlpogePureZetaGammaBridge

/-- Alpöge's conductor-one window estimate composed with the signed peak criterion. -/
theorem omega_riemannHypothesis_from_pure_zeta_windows : RiemannHypothesis :=
  PureZetaGammaBridge.rh_of_pure_zeta_windows PureZetaWindowExtraction.pure_zeta_windows

#print axioms omega_riemannHypothesis_from_pure_zeta_windows
