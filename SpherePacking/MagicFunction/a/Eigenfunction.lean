/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import BlueprintGen
import SpherePacking.MagicFunction.a.Schwartz

open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open scoped FourierTransform

namespace MagicFunction.a.Fourier

section Integral_Permutations

theorem perm_I₁_I₂ : fourierTransformCLE ℂ (I₁ + I₂) = I₃ + I₄ := by sorry

theorem perm_I₅ : fourierTransformCLE ℂ (I₅) = I₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` to prove the reverse.

theorem perm_₃_I₄ : fourierTransformCLE ℂ (I₃ + I₄) = I₁ + I₂ := by sorry

theorem perm_I₆ : fourierTransformCLE ℂ (I₆) = I₅ := by sorry

end Integral_Permutations

section Eigenfunction

/-- $a(x)$ satisfies \ref{eqn:a-fourier}. -/
@[blueprint
  (uses := ["lemma:Gaussian-Fourier"])
  (proof := /--
  We recall that the Fourier transform of a Gaussian function is $$\begin{equation}
  \label{eqn:gaussian Fourier}
      \mathcal{F}(e^{\pi i \|x\|^2 z})(y)=z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z}) }.
  \end{equation}$$ Next, we exchange the contour integration with respect to $z$ variable and Fourier
  transform with respect to $x$ variable in \ref{eqn:a-definition}. This can be
  done, since the corresponding double integral converges absolutely. In this way we obtain
  $$\begin{align}
      \widehat{a}(y)=&\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz
      +\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz\notag \\
      -&2\int\limits_{0}^i\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz +2\int\limits_{i}^{i\infty}\phi_0(z)\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz.\notag
  \end{align}$$ Now we make a change of variables $w=\frac{-1}{z}$. We obtain $$\begin{align}
      \widehat{a}(y)=&\int\limits_{1}^i\phi_0\Big(1-\frac{1}{w-1}\Big)\,(\frac{-1}{w}+1)^2\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw\notag\\
      +&\int\limits_{-1}^i\phi_0\Big(1-\frac{1}{w+1}\Big)\,(\frac{-1}{w}-1)^2\,w^2\,e^{\pi i \|y\|^2 \,w}\,dw\\
      -&2\int\limits_{i \infty}^i\phi_0(w)\,e^{\pi i \|y\|^2 \,w}\,dw +2\int\limits_{i}^{0}\phi_0\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw.\notag
  \end{align}$$ Since $\phi_0$ is $1$-periodic we have $$\begin{align}
      \widehat{a}(y)\,=\,&\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i \|y\|^2 \,z}\,dz
      +\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
      +&2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i \|y\|^2 \,z}\,dz
      -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^{2}\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
      \,=\,&a(y).
  \end{align}$$ This finishes the proof of the proposition.
  -/)
  (latexEnv := "proposition")]
theorem eig_a : fourierTransformCLE ℂ a = a := by
  rw [a_eq_sum_integrals_SchwartzIntegrals]
  have hrw : I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_₃_I₄, perm_I₆]
  ac_rfl

end Eigenfunction
end MagicFunction.a.Fourier
