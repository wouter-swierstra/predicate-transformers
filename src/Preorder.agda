module Preorder where

record Preorder {a : Set} (R : a -> a -> Set) : Set where
  constructor preorder
  field
    pre-refl : (∀ {x} -> R x x)
    pre-trans : (∀ {x y z} -> R x y -> R y z -> R x z)
open Preorder

infixr 2 _⟨_⟩_
_⟨_⟩_ : {a : Set} {b : a -> Set} ->
  {R : ((x : a) -> b x) -> ((x : a) -> b x) -> Set} ->
  (f : (x : a) -> b x) -> {g h : (x : a) -> b x} ->
  R f g -> (Preorder R -> R g h) ->
  (P : Preorder {(x : a) -> b x} R) ->
  R f h
_⟨_⟩_ f {g} {h} step1 step2 P = pre-trans P {f} {g} {h} step1 (step2 P)

_∎ : {a : Set} {b : a -> Set} ->
  (f : (x : a) -> b x) ->
  {R : ((x : a) -> b x) -> ((x : a) -> b x) -> Set} ->
  (P : Preorder {(x : a) -> b x} R) -> R f f
_∎ f P = pre-refl P {f}
