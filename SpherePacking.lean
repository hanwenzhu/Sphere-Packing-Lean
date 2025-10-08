import SpherePacking.Basic.E8
import SpherePacking.Basic.PeriodicPacking
import SpherePacking.Basic.SpherePacking
import SpherePacking.CohnElkies.LPBound
import SpherePacking.CohnElkies.Prereqs
import SpherePacking.ForMathlib.Asymptotics
import SpherePacking.ForMathlib.AtImInfty
import SpherePacking.ForMathlib.Bornology
import SpherePacking.ForMathlib.Cardinal
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.ForMathlib.ENNReal
import SpherePacking.ForMathlib.ENat
import SpherePacking.ForMathlib.Encard
import SpherePacking.ForMathlib.Finsupp
import SpherePacking.ForMathlib.Fourier
import SpherePacking.ForMathlib.FunctionsBoundedAtInfty
import SpherePacking.ForMathlib.InnerProductSpace
import SpherePacking.ForMathlib.InvPowSummability
import SpherePacking.ForMathlib.PoissonSummation.DualLattice
import SpherePacking.ForMathlib.PoissonSummation.EuclideanSpace
import SpherePacking.ForMathlib.PoissonSummation.Lattice_Equiv
import SpherePacking.ForMathlib.PoissonSummation.SchwartzMap
import SpherePacking.ForMathlib.PoissonSummation.Zn_Pi
import SpherePacking.ForMathlib.PoissonSummation.Zn_to_Euclidean
import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
import SpherePacking.ForMathlib.Real
import SpherePacking.ForMathlib.SlashActions
import SpherePacking.ForMathlib.SpecificLimits
import SpherePacking.ForMathlib.UpperHalfPlane
import SpherePacking.ForMathlib.Vec
import SpherePacking.ForMathlib.VolumeOfBalls
import SpherePacking.ForMathlib.ZLattice
import SpherePacking.ForMathlib.tprod
import SpherePacking.MagicFunction.IntegralParametrisations
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Basic
import SpherePacking.MagicFunction.a.Eigenfunction
import SpherePacking.MagicFunction.a.IntegralEstimates.I1
import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.MagicFunction.a.IntegralEstimates.I4
import SpherePacking.MagicFunction.a.IntegralEstimates.I5
import SpherePacking.MagicFunction.a.IntegralEstimates.I6
import SpherePacking.MagicFunction.a.Schwartz
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.b.Basic
import SpherePacking.MagicFunction.b.Eigenfunction
import SpherePacking.MagicFunction.b.Schwartz
import SpherePacking.MagicFunction.b.SpecialValues
import SpherePacking.MagicFunction.b.psi
import SpherePacking.MagicFunction.g.Basic
import SpherePacking.MainTheorem
import SpherePacking.ModularForms.AtImInfty
import SpherePacking.ModularForms.BigO
import SpherePacking.ModularForms.Cauchylems
import SpherePacking.ModularForms.Delta
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.ModularForms.E2
import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.Eisensteinqexpansions
import SpherePacking.ModularForms.Icc_Ico_lems
import SpherePacking.ModularForms.IsCuspForm
import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.ModularForms.clog_arg_lems
import SpherePacking.ModularForms.csqrt
import SpherePacking.ModularForms.equivs
import SpherePacking.ModularForms.eta
import SpherePacking.ModularForms.exp_lems
import SpherePacking.ModularForms.iteratedderivs
import SpherePacking.ModularForms.limunder_lems
import SpherePacking.ModularForms.logDeriv_lems
import SpherePacking.ModularForms.multipliable_lems
import SpherePacking.ModularForms.qExpansion_lems
import SpherePacking.ModularForms.riemannZetalems
import SpherePacking.ModularForms.summable_lems
import SpherePacking.ModularForms.tendstolems
import SpherePacking.ModularForms.tsumderivWithin
import SpherePacking.ModularForms.uniformcts
import SpherePacking.ModularForms.upperhalfplane
import SpherePacking.Tactic.NormNumI
import SpherePacking.Tactic.NormNumI_Scratch
import SpherePacking.Tactic.Test.NormNumI
import BlueprintGen

attribute [blueprint
  (statement := /--
  The *dual lattice* of a lattice $\Lambda$ is the set
  $$\Lambda^* := \setof{v \in \R^d}{\forall l \in \Lambda, \left\langle v,l \right\rangle \in \Z}$$
  -/)] LinearMap.BilinForm.dualSubmodule

attribute [blueprint
  (statement := /--
  A $C^\infty$ function $f:\R^d\to\C$ is called a *Schwartz function* if it decays to zero as
  $\|x\|\to\infty$ faster then any inverse power of $\|x\|$, and the same holds for all partial
  derivatives of $f$, ie, if for all $k, n \in \N$, there exists a constant $C \in \R$ such that for
  all $x \in \R^d$, $\norm{x}^k \cdot \norm{f^{(n)}(x)} \leq C$, where $f^{(n)}$ denotes the $n$-th
  derivative of $f$ considered along with the appropriate operator norm. The set of all Schwartz
  functions from $\R^d$ to $\C$ is called the *Schwartz space*. It is an $\R$-vector space.
  -/)] SchwartzMap

attribute [blueprint
  (uses := [SchwartzMap, Real.fourierIntegral])
  (proof := /--
  We do not elaborate here as the result already exists in Mathlib. We do, however, mention that the
  Lean implementation *defines* a continuous linear equivalence on the Schwartz space *using* the
  Fourier transform (see `SchwartzMap.fourierTransformCLM`). The 'proof' that for any Schwartz
  function $f$, its Fourier transform and its image under this continuous linear equivalence are,
  indeed, the same $\R^d \to \R$ function, is stated in Mathlib solely for the purpose of `rw` and
  `simp` tactics, and is proven simply by `rfl`.
  -/)
  (latexEnv := "lemma")] SchwartzMap.fourierTransformCLM

attribute [blueprint
  (statement := /--
  The *automorphy factor* of weight $k$ is defined as
  $$j_k(z,\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)):=(cz+d)^{-k}.$$
  -/)] UpperHalfPlane.denom

attribute [blueprint
  (statement := /--
  The automorphy factor satisfies the *chain rule*
  $$j_k(z,\gamma_1\gamma_2)=j_k(z,\gamma_1)\,j_k(\gamma_2z,\gamma_1).$$
  -/)
  (uses := [UpperHalfPlane.denom])
  (latexEnv := "lemma")] UpperHalfPlane.denom_cocycle

attribute [blueprint
  (statement := /--
  For all $k$, $E_k\in M_k(\Gamma_1)$. Especially, we have $$\begin{equation}
  \label{eqn:Ek-trans-S}
      E_k \left(-\frac{1}{z}\right) = z^k E_k(z).
  \end{equation}$$
  -/)
  (uses := [ModularForm.eisensteinSeries_MF, ModularForm])
  (proof := /--
  This follows from the fact that the sum converges absolutely. Now apply slash operator with
  $\gamma = \left(\begin{smallmatrix} 0 & -1 \\ 1 & 0 \end{smallmatrix}\right)$ gives
  \ref{eqn:Ek-trans-S}.
  -/)
  (latexEnv := "lemma")] EisensteinSeries.eisensteinSeries_SIF
