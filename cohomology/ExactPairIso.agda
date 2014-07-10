{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness

module cohomology.ExactPairIso where

{- An exact sequence 0 → G → H → 0 implies that G == H -}

module _ {i} {G H : Group i} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _
    (l : is-exact-ktoi-mere
           (ptd-cst {X = Ptd-Lift {j = i} Ptd-Unit}) φ.ptd-f)
    (r : is-exact-ktoi-mere
           φ.ptd-f (ptd-cst {X = H.Ptd-El} {Y = Ptd-Lift {j = i} Ptd-Unit}))
    where

    private
      inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂
      inj = zero-kernel-injective φ
        (λ g p → Trunc-rec (G.El-level _ _) (λ s → ! (snd s)) (l g p))

      image-prop : (h : H.El) → is-prop (Σ G.El (λ g → φ.f g == h))
      image-prop h = all-paths-is-prop $ λ {(g₁ , p₁) (g₂ , p₂) →
        pair= (inj g₁ g₂ (p₁ ∙ ! p₂)) (prop-has-all-paths-↓ (H.El-level _ _))}

      surj : (h : H.El) → Σ G.El (λ g → φ.f g == h)
      surj h = Trunc-rec (image-prop h) (idf _) (r h idp)

    exact-pair-iso : G == H
    exact-pair-iso = surj-inj-iso φ inj surj