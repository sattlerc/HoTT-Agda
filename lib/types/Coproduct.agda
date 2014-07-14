{-# OPTIONS  #-}

open import lib.Basics
open import lib.types.Empty
open import lib.types.Lift
open import lib.types.Pointed

module lib.types.Coproduct where

module _ {i j} {A : Type i} {B : Type j} where

  ⊔-code : Coprod A B → Coprod A B → Type (lmax i j)
  ⊔-code (inl a₁) (inl a₂) = Lift {j = (lmax i j)} $ a₁ == a₂
  ⊔-code (inl a₁) (inr b₂) = Lift Empty
  ⊔-code (inr b₁) (inl a₂) = Lift Empty
  ⊔-code (inr b₁) (inr b₂) = Lift {j = (lmax i j)} $ b₁ == b₂

  ⊔-encode : {x y : Coprod A B} → (x == y) → ⊔-code x y
  ⊔-encode {inl a₁} {y} p = transport (⊔-code $ inl a₁) p (lift $ idp {a = a₁})
  ⊔-encode {inr b₁} {y} p = transport (⊔-code $ inr b₁) p (lift $ idp {a = b₁})

  ⊔-decode : {x y : Coprod A B} → ⊔-code x y → (x == y)
  ⊔-decode {inl _} {inl _} c = ap inl $ lower c
  ⊔-decode {inl _} {inr _} c = Empty-rec $ lower c
  ⊔-decode {inr _} {inl _} c = Empty-rec $ lower c
  ⊔-decode {inr _} {inr _} c = ap inr (lower c)

  ⊔-code-equiv : (x y : Coprod A B) → (x == y) ≃ ⊔-code x y
  ⊔-code-equiv x y = equiv ⊔-encode ⊔-decode (f-g x y) (g-f x y)
    where f-g : ∀ x' y' → ∀ c → ⊔-encode (⊔-decode {x'} {y'} c) == c
          f-g (inl a₁) (inl .a₁) (lift idp) = idp
          f-g (inl a₁) (inr b₂) b = Empty-rec $ lower b
          f-g (inr b₁) (inl a₂) b = Empty-rec $ lower b
          f-g (inr b₁) (inr .b₁) (lift idp) = idp

          g-f : ∀ x' y' → ∀ p → ⊔-decode (⊔-encode {x'} {y'} p) == p
          g-f (inl _) .(inl _) idp = idp
          g-f (inr _) .(inr _) idp = idp

  inl=inl-equiv : (a₁ a₂ : A) → (inl a₁ == inl a₂) ≃ (a₁ == a₂)
  inl=inl-equiv a₁ a₂ = lift-equiv ∘e ⊔-code-equiv (inl a₁) (inl a₂)

  inr=inr-equiv : (b₁ b₂ : B) → (inr b₁ == inr b₂) ≃ (b₁ == b₂)
  inr=inr-equiv b₁ b₂ = lift-equiv ∘e ⊔-code-equiv (inr b₁) (inr b₂)

  inl≠inr : (a₁ : A) (b₂ : B) → (inl a₁ ≠ inr b₂)
  inl≠inr a₁ b₂ p = lower $ ⊔-encode p

  inr≠inl : (b₁ : B) (a₂ : A) → (inr b₁ ≠ inl a₂)
  inr≠inl a₁ b₂ p = lower $ ⊔-encode p

  ⊔-level : ∀ {n} → has-level (S (S n)) A → has-level (S (S n)) B
            → has-level (S (S n)) (Coprod A B)
  ⊔-level pA _ (inl a₁) (inl a₂) =
    equiv-preserves-level ((inl=inl-equiv a₁ a₂)⁻¹) (pA a₁ a₂)
  ⊔-level _ _ (inl a₁) (inr b₂) = λ p → Empty-rec (inl≠inr a₁ b₂ p)
  ⊔-level _ _ (inr b₁) (inl a₂) = λ p → Empty-rec (inr≠inl b₁ a₂ p)
  ⊔-level _ pB (inr b₁) (inr b₂) =
    equiv-preserves-level ((inr=inr-equiv b₁ b₂)⁻¹) (pB b₁ b₂)

_∙⊔_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ∙⊔ Y = ∙[ Coprod (fst X) (fst Y) , inl (snd X) ]

_⊔∙_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊔∙ Y = ∙[ Coprod (fst X) (fst Y) , inr (snd Y) ]


-- Equivalences in a coproduct

equiv-Coprod-l : ∀ {i₁ i₂ j} {A₁ : Type i₁} {A₂ : Type i₂} {B : Type j}
                 → A₁ ≃ A₂ → Coprod A₁ B ≃ Coprod A₂ B
equiv-Coprod-l e = equiv (λ {(inl a₁) → inl (–> e a₁) ; (inr b) → inr b})
                         (λ {(inl a₂) → inl (<– e a₂) ; (inr b) → inr b})
                         (λ {(inl a₂) → ap inl (<–-inv-r e a₂) ; (inr b) → idp})
                         (λ {(inl a₁) → ap inl (<–-inv-l e a₁) ; (inr b) → idp})

equiv-Coprod-r : ∀ {i j₁ j₂} {A : Type i} {B₁ : Type j₁} {B₂ : Type j₂}
                 → B₁ ≃ B₂ → Coprod A B₁ ≃ Coprod A B₂
equiv-Coprod-r e = equiv (λ {(inl a) → inl a ; (inr b₁) → inr (–> e b₁)})
                         (λ {(inl a) → inl a ; (inr b₂) → inr (<– e b₂)})
                         (λ {(inl a) → idp ; (inr b₂) → ap inr (<–-inv-r e b₂)})
                         (λ {(inl a) → idp ; (inr b₁) → ap inr (<–-inv-l e b₁)})

equiv-Coprod : ∀ {i₁ i₂ j₁ j₂}
                 {A₁ : Type i₁} {A₂ : Type i₂}
                 {B₁ : Type j₁} {B₂ : Type j₂}
               → A₁ ≃ A₂ → B₁ ≃ B₂ → Coprod A₁ B₁ ≃ Coprod A₂ B₂
equiv-Coprod ea eb = equiv-Coprod-r eb ∘e equiv-Coprod-l ea

Coprod-comm : ∀ {i j} {A : Type i} {B : Type j} → Coprod A B ≃ Coprod B A
Coprod-comm = equiv (λ {(inl a) → inr a ; (inr b) → inl b})
                    (λ {(inl b) → inr b ; (inr a) → inl a})
                    (λ {(inl b) → idp ; (inr a) → idp})
                    (λ {(inl a) → idp ; (inr b) → idp})


Coprod-l-Empty : ∀ {j} {B : Type j} → Coprod ⊥ B ≃ B
Coprod-l-Empty = equiv (λ {(inl x) → ⊥-rec x ; (inr b) → b})
                       inr
                       (λ _ → idp)
                       (λ {(inl x) → ⊥-rec x ; (inr b) → idp})

Coprod-r-Empty : ∀ {j} {B : Type j} → Coprod B ⊥ ≃ B
Coprod-r-Empty = Coprod-l-Empty ∘e Coprod-comm
