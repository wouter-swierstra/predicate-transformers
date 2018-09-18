{-# OPTIONS --type-in-type #-}
module Spec where
open import Prelude
open import Free

data I {a : Set} (b : a -> Set) : Set where
  Done : ({x : a} -> b x) -> I b
  Spec : (pre : a -> Set) -> (post : (x : a) -> b x -> Set) -> I b

Mix : {a : Set} -> (C : Set) -> (R : C -> Set) -> (a -> Set) -> Set
Mix C R b = Free C R (I b)

spec : ∀ {a} {b : a -> Set} {C : Set} {R : C -> Set} -> (P : a -> Set) -> (Q : (x : a) -> b x -> Set) -> Mix C R b
spec P Q = Pure (Spec P Q)

wpI : {a : Set} -> {b : a -> Set} -> (P : (x : a) -> b x -> Set) -> (x : a) -> I b -> Set
wpI P i (Done o)  = P i o
wpI {a} {b} P i (Spec pre post) =
  Pair (pre i) (post i ⊆ P i)

-- The type of predicate transformers that are generic in the argument of the monad.
PTs : (C : Set) (R : C -> Set) -> Set
PTs C R = {a' : Set} {b' : a' -> Set}
  -> (P : (x : a') -> b' x -> Set)
  -> (x : a') -> Free C R (b' x) -> Set

wpMix : {a : Set} -> {b : a -> Set} -> {C : Set} -> {R : C -> Set}
  -> (PTs C R)
  -> (P : (x : a) -> b x -> Set)
  -> (f : (x : a) -> Mix C R b)
  -> (a -> Set)
wpMix PT P = wp (PT (wpI P))
