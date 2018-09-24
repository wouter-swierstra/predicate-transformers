module Preorder where

record Preorder {a : Set} (R : a -> a -> Set) : Set where
  constructor preorder
  field
    pre-refl : (∀ {x} -> R x x)
    pre-trans : (∀ {x y z} -> R x y -> R y z -> R x z)
open Preorder

infixr 2 _⟨_⟩_
_⟨_⟩_ : {a : Set} ->
  {R : a -> a -> Set} ->
  (f : a) -> {g h : a} ->
  R f g -> (Preorder R -> R g h) ->
  (P : Preorder {a} R) ->
  R f h
_⟨_⟩_ f {g} {h} step1 step2 P = pre-trans P {f} {g} {h} step1 (step2 P)

_∎ : {a : Set} ->
  (f : a) ->
  {R : a -> a -> Set} ->
  (P : Preorder {a} R) -> R f f
_∎ f P = pre-refl P {f}
