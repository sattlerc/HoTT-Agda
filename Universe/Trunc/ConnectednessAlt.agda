{-# OPTIONS --without-K #-}

{- This brief section introduces an alternative definition
   of n-connectedness defined purely using propositional truncation,
   in contrast to the standard one using n-truncations
   (compare Exercise 7.6 in the HoTT book).

   In detail, a type A is usually called n-connected if Trunc n A
   is contractible. Here, we show that n-connectedness of A can also
   be defined recursively as follows:
   * A is (-2)-connected,
   * A is (n+1)-connected iff A is merely inhabited and for all a₀, a₁ : A,
     the path space a₀ == a₁ is n-connected.

   This module is independent from the other files in this directory,
   using only the truncations with definitional computation from the library. -}
module Universe.Trunc.ConnectednessAlt where

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Unit

open import Universe.Utility.General
open import Universe.Utility.TruncUniverse


-- Preliminary lemmata.
module _ where

  -- On proposition, equivalence coincides with logical equivalence.
  prop-equiv : ∀ {i j} {A : ⟨-1⟩ -Type i} {B : ⟨-1⟩ -Type j}
               → (⟦ A ⟧ → ⟦ B ⟧) → (⟦ B ⟧ → ⟦ A ⟧) → ⟦ A ⟧ ≃ ⟦ B ⟧
  prop-equiv {A = (_ , h)} {B = (_ , k)} f g =
    equiv f g (λ _ → prop-has-all-paths k _ _) (λ _ → prop-has-all-paths h _ _)

  -- Equivalent types have equivalent truncatedness propositions.
  equiv-level : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j}
              → A ≃ B → has-level n A ≃ has-level n B
  equiv-level e = prop-equiv {A = (_ , has-level-is-prop)}
                             {B = (_ , has-level-is-prop)}
                             (equiv-preserves-level e)
                             (equiv-preserves-level (e ⁻¹))

  {- The structural lemma for the below equivalence of connectedness notions:
    Contractibility is equivalent to propositionality and mere inhabitation. -}
  contr-decompose : ∀ {i} {A : Type i} → is-contr A ≃ (Trunc ⟨-1⟩ A × is-prop A)
  contr-decompose {i} {A} = prop-equiv {A = U} {B = V} f g where
    U = (_ , is-contr-is-prop)
    V = (_ , Trunc-level) ×-≤ (_ , is-prop-is-prop)
    f = λ c → ([ fst c ] , contr-is-prop c)
    g = λ {(ta , h) → Trunc-rec (snd U) (λ a → inhab-prop-is-contr a h) ta}

-- Everything here will happen in universe Type i.
module _ {i} where
  module _ {n : ℕ₋₂} where
    -- The dependent universal property over n-types.
    Trunc-dup : (A : Type i) (B : (ta : Trunc n A) → n -Type i)
              → Π (Trunc n A) (⟦_⟧ ∘ B) ≃ Π A (⟦_⟧ ∘ B ∘ [_])
    Trunc-dup A B = equiv
      (λ f → f ∘ [_]) (Trunc-elim (snd ∘ B)) (λ _ → idp)
      (λ f → λ= (Trunc-elim (snd ∘ (λ a → Path-≤ (B a) _ _)) (λ a → idp)))

    -- The truncation functor is applicative (here only a special case)
    Trunc-×-equiv : {A B : Type i} → Trunc n (A × B) ≃ (Trunc n A × Trunc n B)
    Trunc-×-equiv {A} {B} = equiv f g f-g g-f where
      f = λ t → (Trunc-fmap fst t , Trunc-fmap snd t)
      g = λ {(ta , tb) → Trunc-rec Trunc-level
                  (λ a → Trunc-rec Trunc-level
                  (λ b → [ (a , b) ]) tb) ta}

      f-g = λ {(ta , tb) → Trunc-elim (λ ta → snd (T (ta , tb)))
                    (λ a → Trunc-elim (λ tb → snd (T ([ a ] , tb)))
                    (λ b → idp) tb) ta} where
        T : Trunc n A × Trunc n B → n -Type i
        T ts = Path-≤ ((_ , Trunc-level) ×-≤ (_ , Trunc-level)) (f (g ts)) ts

      g-f = Trunc-elim (λ _ → snd (Path-≤ (_ , Trunc-level) _ _)) (λ a → idp)

  {- The connectedness predicate from the library:
     is-connected : ℕ₋₂ → Type i → Type i
     is-connected n A = is-contr (Trunc n A) -}

  -- Our connectedness predicate defined using only propositional truncation.
  is-connected' : ℕ₋₂ → Type i → Type i
  is-connected' ⟨-2⟩  A = Lift ⊤
  is-connected' (S n) A = Trunc ⟨-1⟩ A × ((as : A × A) → is-connected' n (fst as == snd as))

  -- Both notions coincide.
  connected-equiv : (n : ℕ₋₂) (A : Type i) → is-connected n A ≃ is-connected' n A
  connected-equiv ⟨-2⟩  A = lift-equiv ⁻¹
                         ∘e contr-equiv-Unit (inhab-prop-is-contr Trunc-level is-contr-is-prop)

  connected-equiv (S n) A = equiv-Σ (fuse-Trunc A _ _) (λ _ → e) ∘e contr-decompose where
    e = is-prop (Trunc (S n) A)
      ≃⟨ curry-equiv ⁻¹ ⟩
        Π (Trunc (S n) A × Trunc (S n) A) (is-contr ∘ uncurry _==_)
      ≃⟨ equiv-Π-l _ (snd Trunc-×-equiv) ⁻¹ ⟩
        Π (Trunc (S n) (A × A)) (is-contr ∘ uncurry _==_ ∘ _)
      ≃⟨ Trunc-dup (A × A) (λ _ → (_ , raise-level-≤T (≤T-ap-S (-2≤T n)) is-contr-is-prop)) ⟩
        ((as : A × A) → is-contr ([ fst as ] == [ snd as ]))
      ≃⟨ equiv-Π-r (λ _ → equiv-level (Trunc=-equiv _ _)) ⟩
        Π (A × A) (is-connected n ∘ uncurry _==_)
      ≃⟨ equiv-Π-r (λ _ → connected-equiv n _) ⟩
        Π (A × A) (is-connected' n ∘ uncurry _==_)
      ≃∎
