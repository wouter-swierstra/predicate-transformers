{-# OPTIONS --type-in-type #-}
module Spec where
import Free
open import Prelude
open import Maybe

open IsMonad

Pre : Set -> Set
Pre a = a -> Set
Post : (a : Set) -> (a -> Set) -> Set
Post a b = (x : a) -> b x -> Set

-- Mix code with specifications.
data Mix (C : Set) (R : C -> Set) (a : Set) : Set where
  Pure : a -> Mix C R a
  Step : (c : C) -> (k : R c -> Mix C R a) -> Mix C R a
  Spec : {a' : Set}
    -> Set
    -> (a' -> Set)
    -> (k : a' -> Mix C R a) -> Mix C R a

fromCode : {C : Set} {R : C -> Set} {a : Set}
  -> Free.Free C R a -> Mix C R a
fromCode (Free.Pure x) = Pure x
fromCode (Free.Step c x) = Step c (λ z → fromCode (x z))

return : {a : Set}
  {C : Set} {R : C -> Set}
  -> a -> Mix C R a
return x = Pure x
spec : ∀ {a} {b : a -> Set}
  {C : Set} {R : C -> Set}
  -> (P : Pre a)
  -> (Q : Post a b)
  -> (x : a) -> Mix C R (b x)
spec {a} {b} P Q x = Spec (P x) (Q x) Pure

-- The type of functions that convert pure postconditions
-- to ones about effects.
PTs : (C : Set) (R : C -> Set) -> Set
PTs C R = (c : C) -> (P : R c -> Set) -> Set

wp : {a : Set} {b : a -> Set}
  -> (P : (x : a) -> b x -> Set)
  -> (f : (x : a) -> b x)
  -> (x : a) -> Set
wp P f x = P x (f x)

fromMaybe : {a : Set} -> (Maybe a) -> (f : a -> Set) -> Set
fromMaybe Nothing f = ⊥
fromMaybe (Just x) f = f x

-- Given a semantics, decide whether the postcondition holds afterwards.
ptMix : {C : Set} {R : C -> Set} {bx : Set}
  -> PTs C R
  -> (P : bx -> Set)
  -> Mix C R bx -> Set
ptMix PT P (Pure y) = P y
ptMix PT P (Step c k) = PT c (\r -> ptMix PT P (k r))
ptMix PT P (Spec {c} pre post k) = Pair pre -- if the precondition holds
  ((z : c) -- and for all intermediate values
    -> post z -- such that the postcondition holds
    -> ptMix PT P (k z)) -- then the continuation makes P hold

-- The weakest precondition for a monadic function.
wpMix : {a : Set} {b : a -> Set} {C : Set} {R : C -> Set}
  -> PTs C R
  -> (P : Post a b)
  -> (f : (x : a) -> Mix C R (b x))
  -> Pre a
wpMix {a} {b} {C} {R} PT P
  = wp (\x -> ptMix PT (P x))

isCode : {C : Set} {R : C -> Set}
  -> {a : Set} -> Mix C R a -> Set
isCode (Pure _) = ⊤
isCode {R = R} (Step c k) = (x : R c) -> isCode (k x)
isCode (Spec _ _ _) = ⊥

run : {C : Set} {R : C -> Set}
  -> {tyO : Set -> Set} -> IsMonad tyO -> (handler : (c : C) -> tyO (R c))
  -> {a : Set} -> (prog : Mix C R a) -> isCode prog
  -> tyO a
run m h (Pure out) prf = pure m out
run m h (Step c k) prf = bind m (h c) \int -> run m h (k int) (prf int)
run _ _ (Spec _ _ _) ()
