/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KrohnRhodes.Foundations.WreathProduct
import KrohnRhodes.Foundations.MonoidWreathBridge
import Mathlib
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.RegularWreathProduct

set_option linter.unusedDecidableInType false

/-!
# The Krasner–Kaloujnine embedding

For a group `G` and a normal subgroup `N`, the Krasner–Kaloujnine homomorphism
`krasnerKaloujnine_hom : G →* N ≀ᵣ (G ⧸ N)` into Mathlib's regular wreath product is
injective (`krasnerKaloujnine_injective`). Combined with the bridge of
`MonoidWreathBridge.lean`, `group_sgdiv_via_normal` shows that a finite `G` divides
`WreathProduct N (G ⧸ N) (G ⧸ N)`; this is the step that splits a finite group along a
normal series.

## Implementation notes

The embedding needs a section `s : G ⧸ N → G` of the quotient map, obtained noncomputably
via `Function.surjInv`. The component `n_g(q) := s(q)⁻¹ * g * s(π(g)⁻¹ * q)` lies in `N`
because its image under `π` is `q⁻¹ * π(g) * π(g)⁻¹ * q = 1`.
-/

namespace KrohnRhodes

universe u


variable {G : Type u} [Group G]

/-! ### Krasner-Kaloujnine universal embedding -/

section Krasner

variable (N : Subgroup G) [N.Normal]

/-- A noncomputable section `G ⧸ N → G` of the quotient map. -/
private noncomputable def section_ : G ⧸ N → G :=
  Function.surjInv (QuotientGroup.mk'_surjective N)

/-- The section is a right inverse of the quotient map. -/
private theorem section_apply (q : G ⧸ N) :
    QuotientGroup.mk' N (section_ N q) = q :=
  Function.surjInv_eq _ _

/-- The "left component" of the Krasner-Kaloujnine homomorphism, before showing
it lands in `N`. -/
private noncomputable def krasnerLeftRaw (g : G) (q : G ⧸ N) : G :=
  (section_ N q)⁻¹ * g * section_ N ((QuotientGroup.mk' N g)⁻¹ * q)

/-- `krasnerLeftRaw g q` lies in `N` (kernel of the quotient map). -/
private theorem krasnerLeftRaw_mem (g : G) (q : G ⧸ N) :
    krasnerLeftRaw N g q ∈ N := by
  -- N = ker(QuotientGroup.mk' N), so it suffices to show mk' applied to the element is 1.
  -- Compute: π(s(q)⁻¹ * g * s(π(g)⁻¹ * q)) = q⁻¹ * π(g) * (π(g)⁻¹ * q) = 1.
  have hone : QuotientGroup.mk' N (krasnerLeftRaw N g q) = 1 := by
    unfold krasnerLeftRaw
    rw [map_mul, map_mul, map_inv, section_apply, section_apply]
    group
  exact (QuotientGroup.eq_one_iff _).mp hone

/-- The "left component" of the Krasner-Kaloujnine homomorphism, valued in `N`. -/
private noncomputable def krasnerLeft (g : G) (q : G ⧸ N) : N :=
  ⟨krasnerLeftRaw N g q, krasnerLeftRaw_mem N g q⟩

/-- The Krasner-Kaloujnine map `G → N ≀ᵣ (G ⧸ N)` (as bare data). -/
private noncomputable def krasnerKaloujnineFun (g : G) : N ≀ᵣ (G ⧸ N) :=
  ⟨krasnerLeft N g, QuotientGroup.mk' N g⟩

/-- Multiplicativity of the Krasner-Kaloujnine map. -/
private theorem krasnerKaloujnine_map_mul (g₁ g₂ : G) :
    krasnerKaloujnineFun N (g₁ * g₂) =
      krasnerKaloujnineFun N g₁ * krasnerKaloujnineFun N g₂ := by
  -- Right component:  π(g₁ g₂) = π(g₁) * π(g₂).
  -- Left component (pointwise at q):
  --   n_{g₁ g₂}(q) = s(q)⁻¹ * g₁ * g₂ * s(π(g₁)⁻¹ π(g₂)⁻¹ q)
  -- = s(q)⁻¹ * g₁ * s(π(g₁)⁻¹ q) * s(π(g₁)⁻¹ q)⁻¹ * g₂ * s(π(g₂)⁻¹ π(g₁)⁻¹ q)
  -- = n_{g₁}(q) * n_{g₂}(π(g₁)⁻¹ q)
  -- Mathlib's regular wreath multiplication: (a * b).left = a.left * (λx, b.left (a.right⁻¹ * x))
  refine RegularWreathProduct.ext ?_ ?_
  · -- left component
    funext q
    apply Subtype.ext
    change krasnerLeftRaw N (g₁ * g₂) q
        = krasnerLeftRaw N g₁ q * krasnerLeftRaw N g₂ ((QuotientGroup.mk' N g₁)⁻¹ * q)
    -- Manual rewriting to avoid timeouts.
    change (section_ N q)⁻¹ * (g₁ * g₂) *
        section_ N ((QuotientGroup.mk' N (g₁ * g₂))⁻¹ * q) =
      ((section_ N q)⁻¹ * g₁ * section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q)) *
      ((section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q))⁻¹ * g₂ *
        section_ N ((QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q)))
    have hquot :
        (QuotientGroup.mk' N (g₁ * g₂))⁻¹ * q =
        (QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q) := by
      rw [map_mul, mul_inv_rev]
      group
    rw [hquot]
    -- Now both sides have the same `section_` arguments.
    set a : G := section_ N q
    set b : G := section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q)
    set c : G := section_ N ((QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q))
    change a⁻¹ * (g₁ * g₂) * c = (a⁻¹ * g₁ * b) * (b⁻¹ * g₂ * c)
    group
  · -- right component
    change QuotientGroup.mk' N (g₁ * g₂) = QuotientGroup.mk' N g₁ * QuotientGroup.mk' N g₂
    exact map_mul (QuotientGroup.mk' N) g₁ g₂

/-- Triviality at 1 of the Krasner-Kaloujnine map. -/
private theorem krasnerKaloujnine_map_one :
    krasnerKaloujnineFun N 1 = 1 := by
  refine RegularWreathProduct.ext ?_ ?_
  · funext q
    apply Subtype.ext
    change (section_ N q)⁻¹ * 1 * section_ N ((QuotientGroup.mk' N 1)⁻¹ * q) = 1
    rw [map_one, inv_one, one_mul, mul_one]
    rw [inv_mul_cancel]
  · change QuotientGroup.mk' N 1 = 1
    exact map_one _

/-- The Krasner-Kaloujnine universal embedding `G →* N ≀ᵣ (G ⧸ N)`. -/
noncomputable def krasnerKaloujnine_hom :
    G →* (N ≀ᵣ (G ⧸ N)) where
  toFun := krasnerKaloujnineFun N
  map_one' := krasnerKaloujnine_map_one N
  map_mul' := krasnerKaloujnine_map_mul N

@[simp] theorem krasnerKaloujnine_hom_left (g : G) (q : G ⧸ N) :
    ((krasnerKaloujnine_hom N g).left q : G) =
      (section_ N q)⁻¹ * g * section_ N ((QuotientGroup.mk' N g)⁻¹ * q) := rfl

/-- Injectivity of the Krasner-Kaloujnine embedding. -/
theorem krasnerKaloujnine_injective :
    Function.Injective (krasnerKaloujnine_hom N) := by
  intro g₁ g₂ h
  -- From φ(g₁) = φ(g₂), read off π(g₁) = π(g₂) and the left components agree.
  have hright : QuotientGroup.mk' N g₁ = QuotientGroup.mk' N g₂ := by
    have := congrArg RegularWreathProduct.right h
    simpa using this
  have hleft : ∀ q : G ⧸ N,
      (krasnerKaloujnine_hom N g₁).left q = (krasnerKaloujnine_hom N g₂).left q := by
    intro q
    have := congrArg RegularWreathProduct.left h
    exact congrFun this q
  -- Take q = 1.
  have h1 : (krasnerKaloujnine_hom N g₁).left 1 = (krasnerKaloujnine_hom N g₂).left 1 := hleft 1
  have hval : ((krasnerKaloujnine_hom N g₁).left 1 : G) =
      ((krasnerKaloujnine_hom N g₂).left 1 : G) := congrArg Subtype.val h1
  rw [krasnerKaloujnine_hom_left, krasnerKaloujnine_hom_left] at hval
  -- The (s(1))⁻¹ on the left and section_ N (mk'⁻¹ * 1) on the right cancel since π(g₁) = π(g₂).
  rw [hright] at hval
  -- s(1)⁻¹ * g₁ * s((mk' g₂)⁻¹) = s(1)⁻¹ * g₂ * s((mk' g₂)⁻¹)
  have hcancel : g₁ = g₂ := by
    have : (section_ N 1)⁻¹ * g₁ * section_ N ((QuotientGroup.mk' N g₂)⁻¹ * 1) =
        (section_ N 1)⁻¹ * g₂ * section_ N ((QuotientGroup.mk' N g₂)⁻¹ * 1) := hval
    -- Cancel: multiply both sides by section_ N 1 on the left and
    -- section_ N (...)⁻¹ on the right.
    set a : G := section_ N 1
    set b : G := section_ N ((QuotientGroup.mk' N g₂)⁻¹ * 1)
    have : a⁻¹ * g₁ * b = a⁻¹ * g₂ * b := this
    have : g₁ = g₂ := by
      have h1 : a * (a⁻¹ * g₁ * b) * b⁻¹ = g₁ := by group
      have h2 : a * (a⁻¹ * g₂ * b) * b⁻¹ = g₂ := by group
      calc g₁ = a * (a⁻¹ * g₁ * b) * b⁻¹ := h1.symm
        _ = a * (a⁻¹ * g₂ * b) * b⁻¹ := by rw [this]
        _ = g₂ := h2
    exact this
  exact hcancel

end Krasner

/-! ### From the embedding to `SgDiv` -/

/-- For a finite group `G` with a normal subgroup `N`, `G` divides
`WreathProduct N (G/N) (G/N)` as a semigroup. -/
theorem group_sgdiv_via_normal {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] :
    SgDiv G (WreathProduct N (G ⧸ N) (G ⧸ N)) := by
  classical
  -- Composition of Krasner embedding and the bridge to monoid wreath.
  set ψ : G →* WreathProduct N (G ⧸ N) (G ⧸ N) :=
    (regularWreath_to_monoidWreath N (G ⧸ N)).comp (krasnerKaloujnine_hom N) with hψdef
  have hbridge_inj : Function.Injective (regularWreath_to_monoidWreath N (G ⧸ N)) :=
    regularWreath_to_monoidWreath_injective N (G ⧸ N)
  have hkras_inj : Function.Injective (krasnerKaloujnine_hom N) :=
    krasnerKaloujnine_injective N
  have hψinj : Function.Injective ψ := fun a b hab => hkras_inj (hbridge_inj hab)
  -- The image of G in WreathProduct as a Subsemigroup.
  refine ⟨{
    carrier := Set.range ψ
    mul_mem' := by
      rintro a b ⟨ga, rfl⟩ ⟨gb, rfl⟩
      exact ⟨ga * gb, ψ.map_mul ga gb⟩ }, ?_, ?_⟩
  · -- Inverse map: range → G via choice (well-defined by injectivity).
    refine
    { toFun := fun u => Function.invFun ψ (u : WreathProduct N (G ⧸ N) (G ⧸ N))
      map_mul' := ?_ }
    intro a b
    obtain ⟨ga, ha⟩ := a.2
    obtain ⟨gb, hb⟩ := b.2
    change Function.invFun ψ ((a * b : { x // x ∈ Set.range ψ }) : WreathProduct N (G ⧸ N) (G ⧸ N))
        = Function.invFun ψ (a : WreathProduct N (G ⧸ N) (G ⧸ N))
          * Function.invFun ψ (b : WreathProduct N (G ⧸ N) (G ⧸ N))
    have hcoe : ((a * b : { x // x ∈ Set.range ψ }) : WreathProduct N (G ⧸ N) (G ⧸ N))
        = ψ (ga * gb) := by
      change (a : WreathProduct N (G ⧸ N) (G ⧸ N)) * (b : WreathProduct N (G ⧸ N) (G ⧸ N))
        = ψ (ga * gb)
      rw [ψ.map_mul, ha, hb]
    rw [hcoe]
    rw [Function.leftInverse_invFun hψinj (ga * gb)]
    rw [← ha, Function.leftInverse_invFun hψinj ga]
    rw [← hb, Function.leftInverse_invFun hψinj gb]
  · -- Surjectivity.
    intro g
    refine ⟨⟨ψ g, g, rfl⟩, ?_⟩
    change Function.invFun ψ (ψ g) = g
    exact Function.leftInverse_invFun hψinj g

end KrohnRhodes
