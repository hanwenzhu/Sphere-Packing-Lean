/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LJCENSE.
Authors: Sidharth Hariharan
-/

import BlueprintGen
import SpherePacking.MagicFunction.b.Schwartz

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

open scoped FourierTransform

namespace MagicFunction.b.Fourier

section Integral_Permutations

theorem perm_J₁_J₂ : fourierTransformCLE ℂ (J₁ + J₂) = -(J₃ + J₄) := by sorry

theorem perm_J₅ : fourierTransformCLE ℂ (J₅) = -J₆ := by sorry

-- Should use results from `RadialSchwartz.Radial` and linearity to prove the reverse.

theorem perm_₃_J₄ : fourierTransformCLE ℂ (J₃ + J₄) = -(J₁ + J₂) := by sorry

theorem perm_J₆ : fourierTransformCLE ℂ (J₆) = -J₅ := by sorry

end Integral_Permutations

section Eigenfunction

/-- $b(x)$ satisfies \ref{eqn:b-fourier}. -/
@[blueprint
  (uses := ["lemma:Gaussian-Fourier", "def:b-definition", "def:psiI-psiT-psiS"])
  (proof := /--
  Here, we repeat the arguments used in the proof of Proposition `MagicFunction.a.Fourier.eig_a`. We
  use identity \ref{eqn:gaussian Fourier} and change contour integration in $z$
  and Fourier transform in $x$. Thus we obtain $$\begin{align}
      \mathcal{F}(b)(x)= & \int\limits_{-1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
          + \int\limits_{1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz \notag \\
      -& 2\,\int\limits_{0}^{i}\psi_I(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
      - 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz. \notag
  \end{align}$$ We make the change of variables $w=\frac{-1}{z}$ and arrive at $$\begin{align}
      \mathcal{F}(b)(x)= & \int\limits_{1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
          + \int\limits_{-1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw \notag \\
      -& 2\,\int\limits_{i\infty}^{i}\psi_I\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
      - 2\,\int\limits_{i}^{0}\psi_S\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw.\notag
  \end{align}$$ Now we observe that the definitions
  \ref{eqn:psiI-define}--\ref{eqn:psiS-define} imply
  $$\begin{align}
      \psi_T|_{-2}S=&-\psi_T \notag \\
      \psi_I|_{-2}S=&\psi_S \notag \\
      \psi_S|_{-2}S=&\psi_I. \notag
  \end{align}$$ Therefore, we arrive at $$\begin{align}
      \mathcal{F}(b)(x)= & \int\limits_{1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz
          + \int\limits_{-1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz \notag \\
      +& 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i \|x\|^2 z}\,dz
      + 2\,\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i \|x\|^2 w}\,dw.\notag
  \end{align}$$ Now from \ref{eqn:b-definition} we see that
  $$\mathcal{F}(b)(x)=-b(x).$$
  -/)
  (latexEnv := "proposition")]
theorem eig_b : fourierTransformCLE ℂ b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end MagicFunction.b.Fourier
