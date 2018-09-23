{-# OPTIONS --type-in-type #-}
module Spec where
import Free
open import Prelude
open import Maybe

-- Running might require special types for input/output.
-- This means Spec needs to be aware of these types.
record RunType : Set where
  constructor types
  field
    tyI : Set -> Set
    prI : {a : Set} -> tyI a -> a
    fmapI : {a : Set} {b : a -> Set} -> (f : (x : a) -> b x)
      -> (x : tyI a) -> tyI (b (prI x))
    prfmapI : {a : Set} -> {b : a -> Set}
      -> (f : (x : a) -> b x) -> (x : tyI a)
      -> f (prI x) == prI (fmapI f x)
    tyO : Set -> Set
    -- TODO: is this a good definition?
    prO : {a : Set} -> tyO a -> Maybe (tyI a)
    fmapO : {a : Set} {b : Set} -> (f : a -> b)
      -> (x : tyI a) -> tyO b
    prfmapO : {a : Set} -> {b : Set}
      -> (f : a -> b) -> (x : tyI a)
      -> Just (f (prI x)) == Maybe.fmap prI (prO (fmapO f x))
    bind : {a b : Set} -> tyO a -> (tyI a -> tyO b) -> tyO b
open RunType

Pre : RunType -> Set -> Set
Pre rt a = tyI rt a -> Set
Post : (rt : RunType) -> (a : Set) -> (b : a -> Set) -> Set
Post rt a b = (x : tyI rt a) -> tyO rt (b (prI rt x)) -> Set

replaceI : {a b : Set} -> (rt : RunType) -> a -> tyI rt b -> tyI rt a
replaceI rt x = fmapI rt (const x)
replaceO : {a b : Set} -> (rt : RunType) -> a -> tyI rt b -> tyO rt a
replaceO rt x = fmapO rt (const x)

prReplaceI : {a b : Set} -> (rt : RunType) -> (x : a) -> (y : tyI rt b)
  -> x == prI rt (replaceI rt x y)
prReplaceI rt x y = prfmapI rt (const x) y

-- Extend wp to running a pure computation in an enhanced context.
{-
wpRT : {a : Set} {b : {a : Set} -> a -> Set} {rt : RunType}
  -> Post rt a b
  -> ((x : a) -> b x)
  -> Pre rt a
wpRT {rt = rt} P f = wp P (lift rt f)
-}

-- Mix code with specifications.
data Mix (C : Set) (R : C -> Set) (rt : RunType) (a : Set) : Set where
  Pure : a -> Mix C R rt a
  Step : (c : C) -> (k : R c -> Mix C R rt a) -> Mix C R rt a
  Spec : {b : Set}
    -> ((t : Set) -> Pre rt t)
    -> ((t : Set) -> Post rt t (K b))
    -> (k : b -> Mix C R rt a) -> Mix C R rt a

fromCode : {C : Set} {R : C -> Set} {rt : RunType} {a : Set}
  -> Free.Free C R a -> Mix C R rt a
fromCode (Free.Pure x) = Pure x
fromCode (Free.Step c x) = Step c (λ z → fromCode (x z))

return : {a : Set}
  {C : Set} {R : C -> Set} {rt : RunType}
  -> a -> Mix C R rt a
return x = Pure x
spec : ∀ {a} {b : a -> Set}
  {C : Set} {R : C -> Set} {rt : RunType}
  -> (P : Pre rt a)
  -> (Q : Post rt a b)
  -> (x : a) -> Mix C R rt (b x)
spec {a} {b} {rt = rt} P Q x = Spec
  (\t tt → P (replaceI rt x tt) )
  (\t i o -> Q (replaceI rt x i) (coerce
    (cong (\x' -> tyO rt (K (b x') i)) (prReplaceI rt x i))
    o))
  Pure

-- The type of functions that convert pure postconditions
-- to ones about effects.
PTs : (C : Set) (R : C -> Set) (rt : RunType) -> Set
PTs C R rt = {b : Set}
  -> (P : tyO rt b -> Set)
  -> (x : tyI rt ⊤)
  -> (c : C) -> (k : R c -> Mix C R rt b) -> Set

wp : {a : Set} {b : a -> Set}
  -> (P : (x : a) -> b x -> Set)
  -> (f : (x : a) -> b x)
  -> (x : a) -> Set
wp P f x = P x (f x)

fromMaybe : {a : Set} -> (Maybe a) -> (f : a -> Set) -> Set
fromMaybe Nothing f = ⊥
fromMaybe (Just x) f = f x

-- Given a semantics, decide whether the postcondition holds afterwards.
ptMix : {C : Set} {R : C -> Set}
  {rt : RunType} {b : Set}
  -> PTs C R rt
  -> (P : tyO rt b -> Set)
  -> (init : tyI rt ⊤) -> Mix C R rt b -> Set
ptMix {rt = rt} PT P init (Pure y) = P (replaceO rt y init)
ptMix {rt = rt} PT P init (Step c k) = PT P (replaceI rt tt init) c k
ptMix {rt = rt} PT P init (Spec {c} pre post k) = Pair (pre ⊤ init) -- if the precondition holds
  ((val : tyO rt c) -- and for all intermediate values
    -> post ⊤ init val -- such that the postcondition holds
    -> fromMaybe (prO rt val) -- and the intermediate is valid
    (\valIn -> ptMix PT P -- then the continuation makes P hold
      (replaceI rt tt valIn)
      (k (prI rt valIn))
    ))

-- The weakest precondition for a monadic function.
wpMix : {a : Set} {b : Set} {C : Set} {R : C -> Set} {rt : RunType}
  -> PTs C R rt
  -> (P : Post rt a (K b))
  -> (f : (x : a) -> Mix C R rt b)
  -> Pre rt a
wpMix {a} {b} {C} {R} {rt} PT P f init
  = wp (\_ -> ptMix PT (P init) (replaceI rt tt init)) f (prI rt init)

isCode : {C : Set} {R : C -> Set} {rt : RunType}
  -> {a : Set} -> Mix C R rt a -> Set
isCode (Pure _) = ⊤
isCode {R = R} (Step c k) = (x : R c) -> isCode (k x)
isCode (Spec _ _ _) = ⊥

run : {C : Set} {R : C -> Set} {rt : RunType}
  -> (handler : tyI rt ⊤ -> (c : C) -> tyO rt (R c))
  -> {a : Set} -> (prog : Mix C R rt a) -> isCode prog
  -> tyI rt ⊤ -> tyO rt a
run {rt = rt} h (Pure out) prf init
  = fmapO rt (λ _ → out) init
run {rt = rt} h (Step c k) prf init
  = bind rt (h init c) \int ->
    run h (k (prI rt int)) (prf (prI rt int)) (replaceI rt tt int)
run _ (Spec _ _ _) ()
