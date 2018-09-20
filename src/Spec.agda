{-# OPTIONS --type-in-type #-}
module Spec where
open import Prelude
open import Free

-- Running might require special types for input/output.
-- This means Spec needs to be aware of these types.
record RunType : Set where
  constructor types
  field
    out : Set -> Set
    inO : {a : Set} -> a -> out a
    liftPre : {a : Set} -> (a -> Set) -> (out a -> Set)
open RunType

-- Lift a pure computation to one in an enhanced context.
lift : {a : Set} {b : a -> Set} {rt : RunType}
  -> ((x : a) -> b x)
  -> ((x : a) -> out rt (b x))
lift {rt = rt} f x = inO rt (f x)

Pre : RunType -> Set -> Set
Pre _ a = a -> Set
Post : RunType -> (a : Set) -> (b : a -> Set) -> Set
Post rt a b = (x : a) -> out rt (b x) -> Set

-- Lift a pure postcondition to an enhanced one.
liftPost : {a : Set} {b : a -> Set}
  -> (rt : RunType)
  -> ((x : a) -> b x -> Set)
  -> Post rt a b
liftPost rt P x = liftPre rt (P x)

-- Extend wp to running a pure computation in an enhanced context.
wpRT : {a : Set} {b : a -> Set} {rt : RunType}
  -> Post rt a b
  -> ((x : a) -> b x)
  -> Pre rt a
wpRT {rt = rt} P f = wp P (lift {rt = rt} f)

data I {a : Set} (rt : RunType) (b : a -> Set) : Set where
  Done : ({x : a} -> b x) -> I rt b
  Spec : (pre : Pre rt a) -> (post : Post rt a b) -> I rt b

Mix : {a : Set} -> (C : Set) -> (R : C -> Set) -> RunType -> (a -> Set) -> Set
Mix C R rt b = Free C R (I rt b)

done : {a : Set} {b : a -> Set} {C : Set} {R : C -> Set} {rt : RunType}
  -> ({x : a} -> b x) -> Mix C R rt b
done x = Pure (Done x)
specI : ∀ {a} {b : a -> Set} {C : Set} {R : C -> Set} {rt : RunType}
  -> (P : Pre rt a)
  -> (Q : Post rt a b)
  -> Mix C R rt b
specI P Q = Pure (Spec P Q)

-- Done for non-dependent types.
doneK : {a b : Set} {C : Set} {R : C -> Set} {rt : RunType}
  -> b -> Mix {a} C R rt (K b)
doneK x = Pure (Done (λ {_} → x))

wpI : {a : Set} -> {b : a -> Set}
  -> {rt : RunType}
  -> (P : Post rt a b)
  -> (f : I rt b)
  -> Pre rt a
wpI {rt = rt} P (Done o) i = P i (inO rt o)
wpI {a} {b} P (Spec pre post) i =
  Pair (pre i) (post i ⊆ P i)

-- Convert a program's behaviour to a postcondition.
match : {a : Set} -> {b : a -> Set} -> {rt : RunType}
  -> (f : I rt b) -> Post rt a b
match {rt = rt} (Done x) i o
  = inO rt x == o
match {rt = rt} (Spec pre post) i o
  = pre i -> post i o

-- The type of functions that convert pure postconditions
-- to ones about effects.
-- Note that this is independent of RunType,
-- (the semantics are independent of the implementation?)
PTs : (C : Set) (R : C -> Set) -> Set
PTs C R = {a : Set} {b : a -> Set}
  -> (P : (x : a) -> (b x) -> Set)
  -> ((x : a) -> Free C R (b x) -> Set)

wpMix : {a : Set} {b : a -> Set} {C : Set} {R : C -> Set} {rt : RunType}
  -> PTs C R
  -> (P : Post rt a b)
  -> (f : (x : a) -> Mix C R rt b)
  -> Pre rt a
wpMix {a} {b} {C} {R} {rt} PT P
  = wpRT {rt = rt} (liftPost rt (PT {b = \x -> I rt b} (flip (wpI P))))
