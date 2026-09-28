/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/
module

public import KrohnRhodes.Defs
public import KrohnRhodes.Foundations.WreathProduct
public import Mathlib
public import KrohnRhodes.Foundations.MonoidWreathBridge
public import KrohnRhodes.Foundations.KrasnerKaloujnine
public import KrohnRhodes.Foundations.Division
public import KrohnRhodes.Foundations.ConstantMaps

/-!
# Cayley's theorem for monoids

* `monoid_faithful_self` — every monoid acts faithfully on itself: the left-regular
  representation `MulAction.toEndHom : N →* Function.End N` is injective.
-/

@[expose] public section

set_option linter.style.show false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace KrohnRhodes


universe u

variable {M : Type u} [Monoid M] [Finite M]


/-- **Every monoid acts faithfully on itself.**  The left-regular
representation `MulAction.toEndHom : N →* Function.End N` (sending `n` to
left-multiplication by `n`) is injective: `n` is recovered as the image of
`1` under left-multiplication by `n`. -/
theorem monoid_faithful_self (N : Type u) [Monoid N] :
    Function.Injective (MulAction.toEndHom (M := N) (α := N)) := by
  intro a b h
  -- `MulAction.toEndHom x` is `(x • ·) = (x * ·)`; evaluate both sides at `1`.
  have h1 : (MulAction.toEndHom (M := N) (α := N) a) (1 : N)
      = (MulAction.toEndHom (M := N) (α := N) b) (1 : N) := by rw [h]
  -- `MulAction.toEndHom x y = x • y = x * y`, so this is `a * 1 = b * 1`.
  show a = b
  have ha : (MulAction.toEndHom (M := N) (α := N) a) (1 : N) = a := by
    show a • (1 : N) = a; rw [smul_eq_mul, mul_one]
  have hb : (MulAction.toEndHom (M := N) (α := N) b) (1 : N) = b := by
    show b • (1 : N) = b; rw [smul_eq_mul, mul_one]
  rw [← ha, ← hb, h1]

end KrohnRhodes
