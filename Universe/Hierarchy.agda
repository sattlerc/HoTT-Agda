{-# OPTIONS --without-K #-}

{- Here, we derive our main theorem: there is a type in the n-th universe
   that is not an n-type, implying the n-th universe is not n-truncated.
   The n-th universe restricted to n-types is hence a 'strict' n-type.
   For this, we first derive local-global looping in a modular way.

   A technical point worth noting is that Agda does not implement
   cumulative universes. Since that means the crucial steps in our
   transformations (where we pass between universes uning univalence)
   can not be expressed using equality without resorting to explicit lifting,
   we decide to explicitely uses equivalences (and pointed equivalences,
   respectively) instead where possible.
   As a drawback, we have to use lemmata showing preservation of
   (pointed) equivalences of various (pointed) type constructions,
   a parametricity property derived for free
   from univalence-induced equalities. -}
module Universe.Hierarchy where

open import lib.Basics
open import lib.Equivalences2
open import lib.NType2
open import lib.types.Bool
open import lib.types.Nat hiding (_+_)
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.TLevel

open import Universe.Utility.General
open import Universe.Utility.Pointed
open import Universe.Utility.TruncUniverse


-- *** Lemma 5.2 ***
{- Our Local-global looping principle.
   We would like to state this principle in the form of
     Ωⁿ⁺¹ (Type i , A) == ∀• a → Ωⁿ (A , a)
   for n ≥ 1. Unfortunately, the two sides have different universe
   levels since (Type i , A) lives in Type• (suc i) instead of Type• i.
   Morally, this is outbalanced by the extra Ω on the left-hand side,
   which might help explain on an intuitive level why
   the n-th universe ends up being not an n-type.
   
   The reason why the univalence principle (A ≡ B) ≃ (A ≃ B)
   cannot be written as (A ≡ B) ≡ (A ≃ B) is precisely the same. -}
module _ {i} {A : Type i} where
  -- The degenerate pre-base case carries around a propositional component.
  Ω-Type : Ω (Type i , A) ≃• Σ• (Π• (A , λ a → (A , a))
                               , (is-equiv , idf-is-equiv _))
  Ω-Type =
      Ω (Type i , A)
    ≃•⟨ ide• _ ⟩
      (A == A , idp)
    ≃•⟨ ua-equiv• ⁻¹• ⟩
      (A ≃ A , ide _)
    ≃•⟨ ide• _ ⟩
      ((Σ (A → A) is-equiv) , (idf _ , idf-is-equiv _))
    ≃•⟨ ide• _ ⟩
      Σ• (Π• (A , λ a → (A , a)) , (is-equiv , idf-is-equiv _))
    ≃•∎

  -- The base case.
  Ω²-Type : (Ω ^ 2) (Type i , A) ≃• Π• (A , λ a → Ω (A , a))
  Ω²-Type =
      (Ω ^ 2) (Type i , A)
    ≃•⟨ equiv-Ω Ω-Type ⟩
      Ω (Σ• (Π• (A , λ a → (A , a)) , (is-equiv , idf-is-equiv _)))
    ≃•⟨ forget-Ω^-Σ•₂ {i} _ 1 (is-equiv-is-prop ∘ _) ⟩
      Ω (Π• (A , λ a → (A , a)))
    ≃•⟨ Ω-Π•-comm _ ⟩
      Π• (A , λ a → Ω (A , a))
    ≃•∎

  -- The general case follows by permuting Ω and Π• repeatedly.
  Ω^-Type : (n : ℕ) → (Ω ^ (n + 2)) (Type i , A)
                   ≃• Π• (A , λ a → (Ω ^ (n + 1)) (A , a))
  Ω^-Type n = Ω^-Π•-comm _ _ n ∘e• equiv-Ω^ n Ω²-Type


{- The pointed family P from the article.
   It takes an n-type A and returns the space of (n+1)-loops
   with basepoint A in U_n^n (the n-th universe restricted to n-types).
   This crucial restriction to n-types implies it is just a set. -}
module _ (n : ℕ) (A : ⟨ n ⟩ -Type ｢ n ｣) where
  -- *** Definition of P and Corollary 5.6 ***
  P : ⟨0⟩ -Type• ｢ n + 1 ｣
  P = Ω^-≤' (n + 1) q where
    q : ⟨ n + 1 ⟩ -Type• ｢ n + 1 ｣
    q = –> Σ-comm-snd ((⟨ n ⟩ -Type-≤ ｢ n ｣ , A))

  -- Forgetting about the truncation level, we may present P as follows:
  Q : Type• ｢ n + 1 ｣
  Q = (Ω ^ (n + 1)) (Type ｢ n ｣ , fst A)

  P-is-Q : fst P ≃• Q
  P-is-Q = equiv-Ω^ n (forget-Ω^-Σ•₂ _ 1 (λ _ → has-level-is-prop))

-- *** Definition of Loop and Lemma 5.7 ***
{- The type Loop of (images of) n-loops in U_(n-1)^(n-1) is
   just the dependent sum over P except for the special case n ≡ 0,
   where we take U_(-1)^(-1) (and hence Loop) to be the booleans.

   The boilerplate with raise-≤T is just to verify Loop n is n-truncated.
   The bulk of the rest of this module consists of showing
   the n-th universe is not n-truncated at basepoint Loop n,
   i.e. that Q n (Loop n) is not contractible.

   Warning: The indexing of Loop starts at -1 in the article,
            but we use natural numbers here (starting at 0),
            thus everything is shifted by one. -}
Loop : (n : ℕ) → ⟨ n ⟩ -Type ｢ n ｣
Loop 0     = (Bool , Bool-is-set)
Loop (S n) = Σ-≤ (⟨ n ⟩ -Type-≤ ｢ n ｣) (λ A →
               raise-≤T {n = ⟨ n + 1 ⟩} (≤T-+2+-l ⟨0⟩ (-2≤T _))
                                        (fst (<– Σ-comm-snd (P n A))))

-- *** Section 2: the base case ***
-- The base case is as usual (there is a non-trivial automorphism on booleans).
base-case : ¬ (is-contr• (Q 0 (Loop 0)))
base-case c = Bool-false≠true false-is-true where
  -- Negation.
  ~ : Bool → Bool
  ~ = λ {true → false; false → true}

  -- Negation is an equivalence.
  e : Bool ≃ Bool
  e = equiv ~ ~ inv inv where
    inv = λ {true → idp; false → idp}

  -- Negation being equal to the identity yields a contradiction.
  false-is-true =
    false             =⟨ ! (coe-β e true) ⟩
    coe (ua e) true   =⟨ ap (λ p → coe p true) (! (c (ua e))) ⟩
    coe idp true      =⟨ idp ⟩
    true              ∎

-- Let us now turn towards the successor case.
module _ (m : ℕ) where
  
  -- We expand the type we are later going to assume contractible.
  Q-L-is-… =
      Q (m + 1) (Loop (m + 1))
    ≃•⟨ ide• _ ⟩
      (Ω ^ (m + 2)) (_ , ⟦ Loop (m + 1) ⟧)
    ≃•⟨ (Ω^-Type m) ⟩
      Π• (_ , λ {(A , q) → Ω ^ (m + 1) $ (⟦ Loop (m + 1) ⟧ , (A , q))})
    ≃•⟨ ide• _ ⟩
      Π• (_ , λ {(A , q) → Ω ^ (m + 1) $ Σ• ((_ , A) , (base ∘ fst ∘ P m , q))})
    ≃•∎

  -- What we really want is to arrive at contractibility of E (m ≥ 1)...
  E = Π• (⟦ Loop (m + 1) ⟧ , λ {(A , q) → Ω ^ (m + 1) $ (⟨ m ⟩ -Type ｢ m ｣ , A)})

  -- ...or at least show that the following element f of E is trivial (m ≡ 0).
  f : base E
  f (_ , q) = q

{- We want to use our assumption of contractibility of Q (n + 1) (Loop (n + 1))
   to show that f is trivial, i.e. constant with value the basepoint. -}
f-is-trivial : (m : ℕ) → is-contr• (Q (m + 1) (Loop (m + 1))) → f m == pt (E m)

-- m ≡ 0
f-is-trivial 0 c = ap (λ f' → fst ∘ f')
                      (! (–> (equiv-is-contr• …-is-E') c f')) where
  {- This is almost E, except for the additional component
      specifying that the first component p should commute with q. -}
  E' = Π• (_ , λ {(A , q) → (Σ (A == A) (λ p → q == q [ (λ x → x == x) ↓ p ])
                                       , (idp , idp))})

  -- This "almost" E comes from Q 1 (Loop 1), hence can be shown contractible.
  …-is-E' : Q 1 (Loop 1) ≃• E'
  …-is-E' = equiv-Π• (ide _ , Ω-Σ•-comm ∘ _) ∘e• Q-L-is-… 0

  {- Fortunately, f can be 'extended' to an element f' of E',
     and triviality of f' implies triviality of f. -}
  f' = λ {(_ , q) → (q , ↓-idf=idf-in (∙=∙' q q))}

{- m ≥ 1: We can show Q (k + 2) (Loop (k + 2)) ≃ E (k + 1),
          thus E is contractible, hence f trivial. -}
f-is-trivial (S k) c = ! (–> (equiv-is-contr• (…-is-E ∘e• Q-L-is-… (k + 1)))
                             c
                             (f (k + 1))) where
  …-is-E : _ ≃• E (k + 1)
  …-is-E = equiv-Π• (ide _ , equiv-Ω^ k ∘ (λ {(A , q) → forget-Ω^-Σ•₂
             {｢ k + 2 ｣} (base ∘ fst ∘ P (k + 1) , q) 2
             (snd ∘ P (k + 1))}))

-- *** Lemma 5.8, part one ***
-- Our main lemma: like in the article, but in negative form.
main : (n : ℕ) → ¬ (is-contr• (Q n (Loop n)))
main 0       = base-case
main (S m) c = main m step where
  {- We know Q (m + 1) (Loop (m + 1)) is contractible,
     use that to show that the above f is trivial,
     deduce f (Loop m , p) ≡ p is trivial for all p in P m (Loop m),
     which implies P m (Loop m) is contractible.
     But this is just another form of Q m (Loop m),
     so the conclusion follows by induction hypothesis. -}
  step : is-contr• (Q m (Loop m))
  step = –> (equiv-is-contr• (P-is-Q m (Loop m)))
            (λ q → app= (! (f-is-trivial m c)) (Loop m , q))

-- *** Lemma 5.8, part two ***
-- Alternate form of the main lemma
main' : (n : ℕ) → ¬ (is-contr• ((Ω ^ (n + 1)) (⟨ n ⟩ -Type ｢ n ｣ , Loop n )))
main' n = main n ∘ –> (equiv-is-contr• (P-is-Q n (Loop n)))


-- Small helper thingy
helpy : ∀ {i} {n : ℕ} {X : Type• i}
        → has-level• (n -1) X → is-contr• ((Ω ^ n) X)
helpy {n = n} {X} = <– contr•-equiv-prop
                  ∘ trunc-many n
                  ∘ transport (λ k → has-level• (k -2) X)
                              (+-comm 1 n)

-- Main theorems now fall out as corollaries.
module _ (n : ℕ) where
  {- Recall that L n is n-truncated.
     We also know it is not (n-1)-truncated, it is thus a 'strict' n-type. -}
  Loop-is-not-trunc : ¬ (has-level (n -1) ⟦ Loop n ⟧)
  Loop-is-not-trunc = main n ∘ helpy ∘ (λ t → universe-=-level t t)

  -- *** Theorem 5.9 ***
  -- The n-th universe is not n-truncated.
  Type-is-not-trunc : ¬ (has-level ⟨ n ⟩ (Type ｢ n ｣))
  Type-is-not-trunc = main n ∘ helpy

  -- *** Theorem 5.11 ***
  {- MAIN RESULT:
     The n-th universe restricted to n-types is a 'strict' (n+1)-type. -}
  Type-≤-is-not-trunc : ¬ (has-level ⟨ n ⟩ (⟨ n ⟩ -Type ｢ n ｣))
  Type-≤-is-not-trunc = main' n ∘ helpy
