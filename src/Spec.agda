{-# OPTIONS --type-in-type #-}
module Spec where
import Free
open import Prelude hiding (_⟨_⟩_)
open import Maybe
open import Preorder

open Preorder.Preorder
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

infixl 20 _>>=_
_>>=_ : {C : Set} {R : C -> Set} -> {a : Set} {b : Set}
  -> Mix C R a -> (a -> Mix C R b) -> Mix C R b
Pure x >>= f = f x
Step c k >>= f = Step c (λ z → k z >>= f)
Spec pre post k >>= f = Spec pre post (λ z → k z >>= f)

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
spec' : {bx : Set} {C : Set} {R : C -> Set}
  -> (P : Set)
  -> (Q : bx -> Set)
  -> Mix C R bx
spec' {a} {b} P Q = Spec P Q Pure

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

isCodeBind :  {C : Set} {R : C -> Set} ->
  {a : Set} {b : Set} ->
  (mx : Mix C R a) -> (f : a -> Mix C R b) ->
  isCode mx -> ((x : a) -> isCode (f x)) ->
  isCode (mx >>= f)
isCodeBind (Pure x) f mxisC fisC = fisC x
isCodeBind (Step c k) f mxisC fisC x = isCodeBind (k x) f (mxisC x) fisC
isCodeBind (Spec pre post k) f ()

run : {C : Set} {R : C -> Set}
  -> {tyO : Set -> Set} -> IsMonad tyO -> (handler : (c : C) -> tyO (R c))
  -> {a : Set} -> (prog : Mix C R a) -> isCode prog
  -> tyO a
run m h (Pure out) prf = pure m out
run m h (Step c k) prf = bind m (h c) \int -> run m h (k int) (prf int)
run _ _ (Spec _ _ _) ()

-- The refinement relation, parametrized over the predicate transformer.
record Refine {C : Set} {R : C -> Set} (PT : PTs C R)
  {a : Set} {b : a -> Set} (f g : (x : a) -> Mix C R (b x)) : Set₁ where
  constructor refinement
  field
    proof : (P : Post a b) -> wpMix PT P f ⊆ wpMix PT P g
record Refine' {C : Set} {R : C -> Set} (PT : PTs C R)
  {bx : Set} (f g : Mix C R bx) : Set₁ where
  constructor refinement'
  field
    proof' : (P : bx -> Set) -> ptMix PT P f -> ptMix PT P g
pre-Refine : {a : Set} {b : a -> Set} {C : Set} {R : C -> Set} {PT : PTs C R} -> Preorder (Refine PT {a = a} {b = b})
Refine.proof (pre-refl pre-Refine) _ _ prf = prf
Refine.proof (pre-trans pre-Refine (refinement fg) (refinement gh)) P x prf = gh P x (fg P x prf)
pre-Refine' : {bx : Set} {C : Set} {R : C -> Set} {PT : PTs C R} -> Preorder (Refine' PT {bx = bx})
Refine'.proof' (pre-refl pre-Refine') _ prf = prf
Refine'.proof' (pre-trans pre-Refine' (refinement' fg) (refinement' gh)) P prf = gh P (fg P prf)

refinePointwise : {C : Set} {R : C -> Set} {PT : PTs C R} {a : Set} {b : a -> Set} {f g : (x : a) -> Mix C R (b x)}
  -> ((x : a) -> Refine' PT (f x) (g x)) -> Refine PT f g
refinePointwise prf = refinement λ P x → Refine'.proof' (prf x) (P x)

sharpenSpec : {a s : Set} {b : Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  {pre pre' : Pair a s -> Set} ->
  {post post' : Pair a s -> Pair b s -> Set} ->
  (∀ i -> pre i -> pre' i) ->
  (∀ i o -> pre i -> post' i o -> post i o) ->
  Refine PT (spec pre post) (spec pre' post')
sharpenSpec {a} {s} {b} {pre} {pre'} {post} {post'} sh we
  = refinement (λ P x z →
    sh x (Pair.fst z) ,
    (λ x₁ x₂ → Pair.snd z x₁ (we x x₁ (Pair.fst z) x₂)))

-- Give an implementation of an (abstract) program, and proof of this fact.
record Impl {C : Set} {R : C -> Set} (PT : PTs C R)
  {a : Set} {b : a -> Set} (spec : (x : a) -> Mix C R (b x)) : Set₁ where
  constructor impl
  field
    prog : (x : a) -> Mix C R (b x)
    code : (x : a) -> isCode (prog x)
    refines : Refine PT spec prog
-- Intermediate step for proving Impl: we have already taken an argument.
record Impl' {C : Set} {R : C -> Set} (PT : PTs C R)
  {bx : Set} (spec : Mix C R bx) : Set₁ where
  constructor impl'
  field
    prog' : Mix C R bx
    code' : isCode prog'
    refines' : Refine' PT spec prog'

-- How to prove Impl PT spec?
-- Generally, we want to take an argument, so given this argument, we do certain operations,
-- and the proof looks like: given \x -> doGet \t -> {!!}
given : {C : Set} {R : C -> Set} {PT : PTs C R} {a : Set} {b : a -> Set} {spec : (x : a) -> Mix C R (b x)}
  -> ((x : a) -> Impl' PT (spec x)) -> Impl PT spec
given prf = impl (λ x → Impl'.prog' (prf x)) (λ x → Impl'.code' (prf x)) (refinePointwise (λ x → Impl'.refines' (prf x)))

doSharpen' : {a s : Set}
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  {pre pre' : Set} ->
  {post post' : a -> Set} ->
  ((P : a -> Set) -> Pair pre ((z : a) -> post z -> P z) -> (Pair pre' ((z : a) -> post' z -> P z))) ->
  Impl' PT (spec' pre' post') ->
  Impl' PT (spec' pre post)
Impl'.prog' (doSharpen' {a} {s} {C} {R} {PT} {pre} _ (impl' prog₁ code₁ (refinement' proof'))) = prog₁
Impl'.code' (doSharpen' {a} {s} {C} {R} {PT} {pre} _ (impl' prog₁ code₁ (refinement' proof'))) = code₁
Refine'.proof' (Impl'.refines' (doSharpen' {a} {s} {C} {R} {PT} {pre} {pre'} {post} {post'} proof'' (impl' prog₁ code₁ (refinement' proof')))) P x = proof' P ((¹ (proof'' P x)) , λ z x₁ → Pair.snd (proof'' P x) z x₁)

doSharpen : {a s : Set} -> {b : a -> Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  {pre pre' : Pre a} ->
  {post post' : Post a b} ->
  ((x : a) -> pre x -> pre' x) ->
  ((x : a) -> (y : b x) -> pre x -> post' x y -> post x y) ->
  Impl PT (spec pre' post') ->
  Impl PT (spec pre post)
doSharpen {a} {s} {pre} {pre'} {post} {post'} x x₁ (impl prog₁ code₁ refines₁) = impl prog₁ code₁
  (refinement λ P x₂ x₃ → Refine.proof refines₁ P x₂ (x x₂ (Pair.fst x₃) , (λ x₄ x₅ → Pair.snd x₃ x₄ (x₁ x₂ x₄ (Pair.fst x₃) x₅))))

doReturn : {a : Set} {b : a -> Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  (post : Post a b) ->
  (f : (x : a) -> b x) ->
  Impl PT (spec (\x -> post x (f x)) post)
doReturn {a} {s} post f = impl
  (\x -> return (f x))
  (λ x → tt)
  (refinement (λ P x z → Pair.snd z (f x) (Pair.fst z)))

doReturn' : {a : Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  (post : a -> Set) ->
  (x : a) -> Impl' PT (spec' (post x) post)
doReturn' {a} {s} post x = impl'
  (return x)
  tt
  (refinement' (λ P z → Pair.snd z x (Pair.fst z)))
