module Preorder where

open import Level

record Preorder {l k : Level} {a : Set l} (R : a -> a -> Set k) : Set (l ⊔ k) where
  constructor preorder
  field
    pre-refl : (∀ {x} -> R x x)
    pre-trans : (∀ {x y z} -> R x y -> R y z -> R x z)
open Preorder

infixr 2 _⟨_⟩_
_⟨_⟩_ : {l k : Level} {a : Set l} ->
  {R : a -> a -> Set k} ->
  (f : a) -> {g h : a} ->
  R f g -> (Preorder R -> R g h) ->
  (P : Preorder {a = a} R) ->
  R f h
_⟨_⟩_ f {g} {h} step1 step2 P = pre-trans P {f} {g} {h} step1 (step2 P)

_∎ : {l k : Level} {a : Set l} ->
  (f : a) ->
  {R : a -> a -> Set k} ->
  (P : Preorder {a = a} R) -> R f f
_∎ f P = pre-refl P {f}
