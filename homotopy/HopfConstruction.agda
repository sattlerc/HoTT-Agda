{-# OPTIONS  #-}

open import HoTT
open import homotopy.HSpace
open import homotopy.PushoutComm using (flip; Pushout-comm)

module homotopy.HopfConstruction {i} (A : Type i) (c : is-connected ⟨0⟩ A)
  (hA : HSpaceStructure A) where

open HSpaceStructure hA
open ConnectedHSpace A c hA

{-
Using the fact that [μ a] is an equivalence, we define a fibration over the
suspension of [A] with fiber [A] and applying [μ a] when you move along
[merid a].
-}

module H = SuspensionRecType A A A μ-equiv

{-
The total space of the previous fibration is the pushout of the following span
(thanks to the flattening lemma).
-}

s : Span
s = span (⊤ × A) (⊤ × A) (A × A)
         (λ cc' → (tt , snd cc')) (λ cc' → (tt , uncurry μ cc'))

lemma : Σ (Suspension A) H.f == Pushout s
lemma = H.flattening

{-
But that span is equal to the following span, which is almost the same as
the span for the join.
-}

x : s == flip (*-span A A)
x = span= (equiv snd (_,_ tt) (λ b → idp) (λ a → idp))
          (equiv snd (_,_ tt) (λ b → idp) (λ a → idp))
          eq (λ a → idp) (λ a → idp)  where

  eq : (A × A) ≃ (A × A)
  eq = equiv to from to-from from-to  where

    to : A × A → A × A
    to (a , a') = (μ a a' , a')

    from : A × A → A × A
    from (a , a') = (<– (μ'-equiv a') a , a')

    to-from : (a : A × A) → to (from a) == a
    to-from (a , a') = pair×= (<–-inv-r (μ'-equiv a') a) idp

    from-to : (a : A × A) → from (to a) == a
    from-to (a , a') = pair×= (<–-inv-l (μ'-equiv a') a) idp

lemma2 : (A * A) ≃ (Pushout (flip (*-span A A)))
lemma2 = Pushout-comm (*-span A A)

theorem : Σ (Suspension A) H.f == (A * A)
theorem = lemma ∙ ap Pushout x ∙ ! (ua lemma2)

-- record FibSeq {i j k ℓ} (A : Type i) (B : Type j) (C : Type k) (c : C)
--   : Type (lmax (lmax i j) (lmax k (lsucc ℓ))) where
--   constructor fibSeq
--   field
--     fibration : C → Type ℓ
--     fiber : fibration c ≃ A
--     total : Σ C fibration ≃ B
