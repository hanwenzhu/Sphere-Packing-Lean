import BlueprintGen
import SpherePacking.Basic.E8

open SpherePacking E8

/-- $\Delta_8 = \Delta_{E_8}$. -/
@[blueprint
  (uses := ["corollary:upper-bound-E8"])
  (proof := /--
  By definition, $\Delta_{E_8} \leq \Delta_8$, while
  \ref{corollary:upper-bound-E8} shows
  $\Delta_8 = \sup_{\mathrm{packing} \, \mathcal{P}} \leq \Delta_{E_8}$, and the result follows.
  -/)
  (latexEnv := "corollary")]
theorem SpherePacking.MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  sorry
