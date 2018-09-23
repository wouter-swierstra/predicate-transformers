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
  {P : Preorder {(x : a) -> b x} R} ->
  (f : (x : a) -> b x) -> {g h : (x : a) -> b x} ->
  R f g -> R g h -> R f h
_⟨_⟩_ {P = P} f {g} {h} step1 step2 = pre-trans P {f} {g} {h} step1 step2

_∎ : {a : Set} {b : a -> Set} ->
  {R : ((x : a) -> b x) -> ((x : a) -> b x) -> Set} ->
  {P : Preorder {(x : a) -> b x} R} ->
  (f : (x : a) -> b x) -> R f f
_∎ {P = P} f = pre-refl P {f}
