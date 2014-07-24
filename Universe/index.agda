{-# OPTIONS --without-K #-}

{- *** Definition 5.3 and Lemma 5.5 are taken from the library ***
   *** Corollary 6.8 is too trivial a consequence of -}

{- ConnectednessAlt and the last submodule of Connection are the
   only modules importing real truncation types from the library.
   Except for that, Univalence is the only additional assumption
   to Agda-style MLTT we work with. -}
module Universe.index where

{- General utility funcions and type constructors for
   the pseudo-universe of types of fixed truncation level. -}
import Universe.Utility.General
import Universe.Utility.TruncUniverse

{- Pointed types.
   Corresponds to section 4 plus some lemmata of section 5,
   which are used in multiple modules and thus belong here. -}
-- *** Definitions 4.1, 4.3, 4.5, 4.6 and Lemmata 4.5, 4.7, 5.1, 5.4 ***
import Universe.Utility.Pointed

{- Homotopically complicated types.
   Corresponds to section 5 sans the initial lemma.
   Concludes with the main theorem that the n-types
   in the n-th universe from a strict n-type.
   Hierarchy and Trunc.* are mutually independent. -}
{- *** Lemmata 5.2, 5.7, 5.8(*), Theorems 5.9, 5.11, and Corollary 5.6 ***
       (*) a slightly weaker version -}
import Universe.Hierarchy

{- Connectedness constructions
   Corresponds to section 6 and 7.
   The first three modules develop a framework of
   truncations internal to MLTT+Univalence without truncations.
   Connection contains the main result of section 6.
   ConnectednessAlt is independent from the first four modules
   and presents a provably equivalent definition of n-connectedness
   using only propositional truncation (as remarked in the article
   and mentioned in an exercise in the HoTT book). -}

--- *** Definition 6.2, Lemma 6.6
import Universe.Trunc.Universal

--- *** Definition 6.4, Lemma 6.7 ***
import Universe.Trunc.Basics

--- *** Lemmata 6.9, 6.10
import Universe.Trunc.TypeConstructors

--- *** Definitions 6.11, 6.13, Lemmata 6.12, 6.14, 6.15
import Universe.Trunc.Connection
import Universe.Trunc.ConnectednessAlt
