/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import BlueprintGen
import SpherePacking.MagicFunction.a.Schwartz

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions

namespace MagicFunction.a.SpecialValues

section Zero

/-- We have $a(0) = -\frac{i}{8640}$. -/
@[blueprint
  (uses := ["prop:a-another-integral"])
  (proof := /-- These identities follow immediately from the previous proposition. -/)
  (latexEnv := "proposition")]
theorem a_zero : a 0 = -8640 * I / π := by sorry

end Zero
end MagicFunction.a.SpecialValues
