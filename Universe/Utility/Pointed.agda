{-# OPTIONS --without-K #-}

{- This module serves to develop some basic theory about pointed types.
   After defining the usual notions of pointed types, pointed equivalences,
   and loop spaces, we derive a version of univalence for pointed equivalences
   and observe that univalence between identical types is a pointed equivalence.

   We define pointed versions of dependent sums and products using the usual
   notion of pointed predicates and observe that they commute in a certain sense
   with taking loop spaces.

   We finish by deriving a generalization to n-truncation and n-th loop spaces
   of the fact allowing us to 'forget' contractible components in a dependent
   sum type that will be needed in the Hierarchy module. -}
module Universe.Utility.Pointed where

open import lib.Basics
open import lib.NType2
open import lib.types.Nat hiding (_+_)
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel

open import Universe.Utility.General
open import Universe.Utility.TruncUniverse


{- Pointed types.
   A pointed type is a type (base) together with a chosen element (pt).
   The loop space construction Ω takes a pointed type and returns the type
   of all loops at the given basepoint. The trivial loop is taken as
   canonical element, thus forming a new pointed type. -}
Type• : (i : ULevel) → Type (lsucc i)
Type• i = Σ (Type i) (idf _)

module _ {i} (X : Type• i) where
  base = fst X
  pt   = snd X

-- Alternate definition: Σ (n -Type i) ⟦_⟧
_-Type•_ : (n : ℕ₋₂) (i : ULevel) → Type (lsucc i)
n -Type• i = Σ (Type• i) (has-level n ∘ base)

-- For alternate definition: Σ-≤ (n -Type-≤ i) raise
_-Type•-≤_ : (n : ℕ₋₂) (i : ULevel) → S n -Type lsucc i
n -Type•-≤ i = (n -Type• i
              , equiv-preserves-level Σ-comm-snd
                                      (snd (Σ-≤ (n -Type-≤ i) raise)))

{- Pointed equivalences.
   An equivalence of pointed types is an equivalences of the bases
   that preserves the points -}
_≃•_ : ∀ {i j} → Type• i → Type• j → Set (i ⊔ j)
A ≃• B = Σ (base A ≃ base B) (λ f → –> f (pt A) == pt B)

ide• : ∀ {i} (X : Type• i) → X ≃• X
ide• _ = ide _ , idp

_∘e•_ : ∀ {i j k} {X : Type• i} {Y : Type• j} {Z : Type• k}
       → Y ≃• Z → X ≃• Y → X ≃• Z
(u , p) ∘e• (v , q) = (u ∘e v , ap (–> u) q ∙ p)

_⁻¹• : ∀ {i j} {X : Type• i} {Y : Type• j} → X ≃• Y → Y ≃• X
(u , p) ⁻¹• = (u ⁻¹ , ap (<– u) (! p) ‌∙ <–-inv-l u _)

-- Equational reasoning for pointed equivalences.
infix  2 _≃•∎
infixr 2 _≃•⟨_⟩_

_≃•⟨_⟩_ : ∀ {i j k} (X : Type• i) {Y : Type• j} {Z : Type• k}
          → X ≃• Y → Y ≃• Z → X ≃• Z
_ ≃•⟨ u ⟩ v = v ∘e• u

_≃•∎ : ∀ {i} (X : Type• i) → X ≃• X
_≃•∎ = ide•


-- The loop space construction.
Ω : ∀ {i} → Type• i → Type• i
Ω (A , a) = (a == a , idp)

Ω-≤ : ∀ {i} {n : ℕ₋₂} → (S n) -Type• i → n -Type• i
Ω-≤ ((A , a) , t) = (Ω (A , a) , t a a)

-- Loop spaces are preserved by pointed equivalences.
equiv-Ω : ∀ {i j} {X : Type• i} {Y : Type• j} → X ≃• Y → Ω X ≃• Ω Y
equiv-Ω (u , p) = split u p where
  split : ∀ u {a} {b} → –> u a == b → Ω (_ , a) ≃• Ω (_ , b)
  split u idp = (equiv-ap u _ _ , idp)

equiv-Ω^ : ∀ {i j} {X : Type• i} {Y : Type• j} (n : ℕ)
           → X ≃• Y → (Ω ^ n) X ≃• (Ω ^ n) Y
equiv-Ω^ 0     e = e
equiv-Ω^ (S n) e = equiv-Ω^ n (equiv-Ω e)


{- We call a pointed type n-truncated if its base is.
   Constructing the loop space decrements the truncation level. -}
has-level• : ∀ {i} → ℕ₋₂ → Type• i → Type i
has-level• n = has-level n ∘ base

trunc-many : ∀ {i} {X : Type• i} {k : ℕ} (n : ℕ)
             → has-level• (k + n -2)          X
             → has-level• (k     -2) ((Ω ^ n) X)
trunc-many 0     t = t
trunc-many (S n) t = trunc-many n (t _ _)

--Ω^-≤ : ∀ {i} {k : ℕ} (n : ℕ) → (k + n -2) -Type• i → (k -2) -Type• i
--Ω^-≤ O     X = X
--Ω^-≤ (S n) X = Ω^-≤ n (Ω-≤ X)

Ω^-≤ : ∀ {i} {k : ℕ} (n : ℕ) → (k + n -2) -Type• i → (k -2) -Type• i
Ω^-≤ n (X , t) = ((Ω ^ n) X , trunc-many n t)

Ω^-≤' : ∀ {i} {k : ℕ} (n : ℕ) → (n + k -2) -Type• i → (k -2) -Type• i
Ω^-≤' n (X , t) =
  ((Ω ^ n) X , trunc-many n (transport (λ z → has-level• (z -2) X)
                                       (+-comm _ n) t))


{- Pointedness allows for a more direct notion of contractibility.
   Since pointed types are always inhabited,
   being contractible and propositional is equivalent. -}
module _ {i} (X : Type• i) where
  is-contr• : Type i
  is-contr• = ∀ a → a == pt X

  prop-is-contr• : has-level• ⟨-1⟩ X → is-contr•
  prop-is-contr• t _ = prop-has-all-paths t _ _

-- Pointed equivalences preserve (pointed) contractibility.
equiv-is-contr• : ∀ {i j} {X : Type• i} {Y : Type• j}
                → X ≃• Y → is-contr• X ≃ is-contr• Y
equiv-is-contr• (u , p) = equiv-Π u (λ a → (_ , post∙-is-equiv p)
                                        ∘e (_ , pre∙-is-equiv (<–-inv-r u a)) ⁻¹
                                        ∘e equiv-ap u _ _)


-- Univalence for pointed equivalences.
module _ {i} {A B : Type• i} where
  ua•-equiv : (A ≃• B) ≃ (A == B)
  ua•-equiv = 
      A ≃• B
    ≃⟨ ide _ ⟩
      Σ (base A ≃ base B) (λ f → –> f (pt A) == pt B)
    ≃⟨ equiv-Σ-fst _ (snd (ua-equiv ⁻¹)) ⁻¹ ⟩
      Σ (base A == base B) (λ q → coe q (pt A) == pt B)
    ≃⟨ equiv-Σ-snd (λ q → coe-equiv (ap (λ f → coe f (pt A) == pt B)
                                        (! (ap-idf q)))) ⟩
      Σ (base A == base B) (λ q → coe (ap (idf _) q) (pt A) == pt B)
    ≃⟨ equiv-Σ-snd (λ q → to-transp-equiv _ q ⁻¹) ⟩
      Σ (base A == base B) (λ q → pt A == pt B [ idf _ ↓ q ])
    ≃⟨ =Σ-eqv _ _ ⟩
      A == B
    ≃∎

  ua• : A ≃• B → A == B
  ua• = –> ua•-equiv

  coe•-equiv : A == B → A ≃• B
  coe•-equiv = <– ua•-equiv

-- Normal univalence can be made pointed in the endo-setting.
module _ {i} {A : Type i} where
  ua-equiv• : (A ≃ A , ide _) ≃• (A == A , idp)
  ua-equiv• = ((ua-equiv ⁻¹) , idp) ⁻¹•


{- Pointed predicates.
   A pointed predicate over a pointed type is a predicate over the base
   together with a inhabitant of the predicate at the point.
   Note that pointed types are equivalent to pointed predicates
   over the pointed unit type (not shown here). -}
Pred• : ∀ {i} (X : Type• i) (j : ULevel) → Type (i ⊔ lsucc j)
Pred• X j = Σ (base X → Type j) (λ P → P (pt X))

-- We have fibered notions of the loop space contruction and n-truncatedness.
module _ {i} {X : Type• i} {j} where
  Ω̃ : Pred• X j → Pred• (Ω X) j
  Ω̃ (P , x) = ((λ p → x == x [ P ↓ p ]) , idp)

  pred-has-level : ℕ₋₂ → Pred• X j → Type (i ⊔ j)
  pred-has-level n Q = (a : base X) → has-level n (fst Q a)


{- == Pointed dependent sums ==
   Pointed predicates as defined above enable us to introduce a Σ-connective
   for pointed types. Because of the abstract nature of some of our lemmata, we
   give Σ• in its uncurried form and first define the type of its parameter. -}
Σ•-param : ∀ i j → Type (lsucc (i ⊔ j))
Σ•-param i j = Σ (Type• i) (λ X → Pred• X j)

module _ {i j} where
  Ω-Σ•-param : Σ•-param i j → Σ•-param i j
  Ω-Σ•-param (X , W) = (Ω X , Ω̃ W)

  Σ• : Σ•-param i j → Type• (i ⊔ j)
  Σ• (X , Q) = (Σ (base X) (fst Q) , (pt X , snd Q))
  
  {- Commutativity of pointed dependent sums and the loop space construction
     will become an important technical tool, enabling us to work at a more
     abstract level later on. -}
  Ω-Σ•-comm : (R : Σ•-param i j) → Ω (Σ• R) ≃• Σ• (Ω-Σ•-param R)
  Ω-Σ•-comm _ = (=Σ-eqv _ _ , idp) ⁻¹•


{- Pointed dependent products.
   This is not quite the equivalent of Π for pointed types: the domain parameter
   is just an ordinary non-pointed type. However, to enable our goal of
   abstractly working with pointed types, defining this notion is useful. -}
Π•-param : ∀ i j → Type (lsucc (i ⊔ j))
Π•-param i j = Σ (Type i) (λ A → A → Type• j)

module _ {i j} where
  Ω-Π•-param : Π•-param i j → Π•-param i j
  Ω-Π•-param (A , F) = (A , Ω ∘ F)

  Π• : Π•-param i j → Type• (i ⊔ j)
  Π• (A , Y) = (Π A (base ∘ Y) , pt ∘ Y)

  {- Pointed dependent products and loop space construction on
     its codomain parameter commute as well. -}
  Ω-Π•-comm : (R : Π•-param i j) → Ω (Π• R) ≃• Π• (Ω-Π•-param R)
  Ω-Π•-comm _ = (app=-equiv , idp)

  Ω^-Π•-comm : (C : Type i) (F : C → Type• j) (n : ℕ)
             → (Ω ^ n) (Π• (C , F)) ≃• Π• (C , Ω ^ n ∘ F)
  Ω^-Π•-comm C F 0     = ide• _
  Ω^-Π•-comm C F (S n) = Ω^-Π•-comm C _ n ∘e• equiv-Ω^ n (Ω-Π•-comm _)

equiv-Π• : ∀ {i₀ i₁ j₀ j₁} {R₀ : Π•-param i₀ j₀} {R₁ : Π•-param i₁ j₁}
           → Σ (fst R₀ ≃ fst R₁) (λ u → ∀ a → snd R₀ (<– u a) ≃• snd R₁ a)
           → Π• R₀ ≃• Π• R₁
equiv-Π• (u , v) = (equiv-Π u (fst ∘ v) , λ= (snd ∘ v))


-- In an n-th loop space, we can forget components of truncation level n.
forget-Ω^-Σ•₂ : ∀ {i j} {X : Type• i} (Q : Pred• X j) (n : ℕ)
                → pred-has-level (n -2) Q → (Ω ^ n) (Σ• (X , Q)) ≃• (Ω ^ n) X
forget-Ω^-Σ•₂     {X = X} Q    O  h = (Σ₂-contr h , idp)
forget-Ω^-Σ•₂ {i} {X = X} Q (S n) h =
  (Ω ^ (S n)) (Σ• (X , Q))  ≃•⟨ equiv-Ω^ n (Ω-Σ•-comm _) ⟩
  (Ω ^ n) (Σ• (Ω X , Ω̃ Q))  ≃•⟨ forget-Ω^-Σ•₂ {i} _ n (λ _ → =-[-↓-]-level h) ⟩
  (Ω ^ (S n)) X             ≃•∎
