{-# OPTIONS --type-in-type #-}

module SliceSpec where

-- Spec in a slice category over a Set.
-- The difference with Spec is that we don't want to return a value
-- but a pure computation.

open import Prelude hiding (_⟨_⟩_)
open import Preorder

open IsMonad
open Preorder.Preorder

-- Slice ⊤ should be isomorphic to Mix
-- The meaning of Slice a C R b x is:
--  a : type to take the slice over
--  C : choices to take in computation
--  R : return type of a choice
--  b : return type of the computation
data Slice (a : Set) (C : Set) (R : C -> Set) (b : Set) : Set where
  Pure : b -> Slice a C R b
  Step : (c : C) (k : R c -> Slice a C R b) -> Slice a C R b
  Spec : {b' : Set} ->
    (pre : a -> Set) (post : a -> b' -> a -> Set) ->
    (k : b' -> Slice a C R b) -> Slice a C R b

instance
  IsMonad-Slice : ∀ {a C R} → IsMonad (Slice a C R)
  IsMonad-Slice = isMonad _>>='_ Pure refl right-identity'
    where
    _>>='_ : {a : Set} {C : Set} {R : C -> Set} ->
      {b : Set} {c : Set} ->
      Slice a C R b -> (b -> Slice a C R c) -> Slice a C R c
    Pure x >>=' f = f x
    Step c k >>=' f = Step c λ z → k z >>=' f
    Spec pre post k >>=' f = Spec pre post λ z → k z >>=' f
    right-identity' : ∀ {a C R b} {mx : Slice a C R b} → mx >>=' Pure == mx
    right-identity' {mx = Pure x} = refl
    right-identity' {mx = Step c k} = cong (Step c) (extensionality (λ x → right-identity'))
    right-identity' {mx = Spec pre post k} = cong (Spec pre post) (extensionality (λ x → right-identity'))

spec : {a : Set} {b : Set} {C : Set} {R : C -> Set} ->
  (P : a -> Set) (Q : a -> b -> a -> Set) ->
  Slice a C R b
spec P Q = Spec P Q Pure

PTs : (a : Set) -> (C : Set) (R : C -> Set) -> Set
PTs a C R = (c : C) -> (P : R c -> a -> Set) -> a -> Set

-- Does the computation satisfy the predicate on the initial given value?
ptSlice : {a : Set} {b : Set} ->
  {C : Set} {R : C -> Set} ->
  PTs a C R ->
  (Q : b -> a -> Set) ->
  Slice a C R b -> a -> Set
ptSlice PT Q (Pure y) x = Q y x
ptSlice PT Q (Step c k) x = PT c (λ y x' → ptSlice PT Q (k y) x') x
ptSlice {a = a} PT Q (Spec {c} pre post k) x = Pair (pre x)
  ((x' : a) (z : c) ->
    post x z x' ->
    ptSlice PT Q (k z) x')

isCodeSlice : {a : Set} {C : Set} {R : C -> Set} ->
  {b : Set} -> Slice a C R b -> Set
isCodeSlice (Pure y) = ⊤
isCodeSlice {R = R} (Step c k) = (r : R c) -> isCodeSlice (k r)
isCodeSlice (Spec pre post k) = ⊥

isCodeBind : {a : Set} {C : Set} {R : C -> Set} ->
  {b c : Set} -> (mx : Slice a C R b) -> (f : b -> Slice a C R c) ->
  isCodeSlice mx -> ((y : b) -> isCodeSlice (f y)) ->
  isCodeSlice (mx >>= f)
isCodeBind (Pure x₂) f x x₁ = x₁ x₂
isCodeBind (Step c k) f x x₁ = λ r → isCodeBind (k r) f (x r) x₁
isCodeBind (Spec pre post k) f x x₁ = x

runSlice : {a : Set} {C : Set} {R : C -> Set} ->
  {tyO : Set -> Set} -> IsMonad tyO -> (handler : (x : a) -> (c : C) -> tyO (Pair (R c) a))
  {b : Set} -> (prog : Slice a C R b) -> isCodeSlice prog ->
  a -> tyO (Pair b a)
runSlice m h (Pure y) tt x = pure m (y , x)
runSlice m h (Step c k) prf x = bind m (h x c) λ z → runSlice m h (k (Pair.fst z)) (prf (Pair.fst z)) (Pair.snd z)
runSlice m h (Spec pre post k) ()

record Refine {a : Set} {C : Set} {R : C -> Set} (PT : PTs a C R)
  {bx : Set} (f g : Slice a C R bx) : Set₁ where
  constructor refinement
  field
    proof : (P : a -> bx -> a -> Set) -> (x : a) -> ptSlice PT (P x) f x -> ptSlice PT (P x) g x
pre-Refine : {a bx : Set} {C : Set} {R : C -> Set} {PT : PTs a C R} -> Preorder (Refine PT {bx = bx})
Refine.proof (pre-refl pre-Refine) _ x prf = prf
Refine.proof (pre-trans pre-Refine (refinement fg) (refinement gh)) P x prf = gh P x (fg P x prf)

record Impl {a : Set} {C : Set} {R : C -> Set} (PT : PTs a C R)
  {bx : Set} (spec : Slice a C R bx) : Set₁ where
  constructor impl
  field
    prog : Slice a C R bx
    code : isCodeSlice prog
    refines : Refine PT spec prog

doSharpen : {a : Set} {C : Set} {R : C -> Set} {PT : PTs a C R} ->
  {b : Set} -> {pre pre' : a -> Set} {post post' : a -> b -> a -> Set} ->
  (∀ t -> pre t -> pre' t) ->
  (∀ t x t' -> pre t -> post' t x t' -> post t x t') ->
  Impl PT (spec pre' post') -> Impl PT (spec pre post)
doSharpen {pre} {pre'} {post} {post'} preI postI (impl prog code (refinement proof)) = impl
  prog
  code
  (refinement λ P x₂ x₃ → proof P x₂ (preI x₂ (Pair.fst x₃) , (λ x' z z₁ → Pair.snd x₃ x' z (postI x₂ z x' (Pair.fst x₃) z₁))))

doReturn : {a : Set} {C : Set} {R : C -> Set} {PT : PTs a C R} ->
  {b : Set} -> {pre : a -> Set} {post : a -> b -> a -> Set} ->
  (y : b) -> (∀ t -> pre t -> post t y t) ->
  Impl PT (spec pre post)
doReturn y prf = impl (Pure y) tt (refinement (λ P x z → Pair.snd z x y (prf x (Pair.fst z))))
