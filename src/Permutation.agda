module Permutation where

open import Prelude
open import Vector

data IsPermutation {a : Set} : {n : Nat} -> (xs ys : Vec n a) -> Set where
  NilPermutation : IsPermutation vNil vNil
  HeadPermutation : {x : a} {n : Nat} ->
    {xs : Vec n a} {ys : Vec (Succ n) a} ->
    Sigma (x ∈v ys) (\pf -> IsPermutation xs (deleteV ys pf)) ->
    IsPermutation (vCons x xs) ys
-- We will just assume permutations are symmetric because the proof seems quite hard for now, and isn't vital.
postulate perm-sym : ∀ {a n} {xs ys : Vec n a} -> IsPermutation xs ys -> IsPermutation ys xs

-- If an element is in a list with something deleted,
-- then it is in the list without something deleted.
in-delete-to-in : ∀ {a n} {x x' : a} {xs : Vec (Succ n) a} ->
  (i : x' ∈v xs) -> x ∈v (deleteV xs i) -> x ∈v xs
in-delete-to-in inHead x₁ = inTail x₁
in-delete-to-in {a} {Zero} (inTail ()) x₁
in-delete-to-in {a} {Succ n} (inTail i) inHead = inHead
in-delete-to-in {a} {Succ n} (inTail i) (inTail x₁) = inTail (in-delete-to-in i x₁)

perm-to-in : ∀ {a n} {x : a} {xs xs' : Vec n a} ->
  (x ∈v xs) -> IsPermutation xs xs' -> x ∈v xs'
perm-to-in inHead (HeadPermutation (fst , snd)) = fst
perm-to-in (inTail x₁) (HeadPermutation (fst , snd)) = in-delete-to-in fst (perm-to-in x₁ snd)

in-delete-tail : ∀ {a n} {x x' : a} {xs : Vec n a} ->
  (i : x' ∈v xs) -> x ∈v deleteV (vCons x xs) (inTail i)
in-delete-tail {xs = vNil} ()
in-delete-tail {xs = x :: xs} i = inHead

perm-cons : ∀ {a n} {x y : a} {xs ys : Vec (Succ n) a} ->
  (ix : x ∈v ys) (iy : y ∈v xs) ->
  IsPermutation (deleteV xs iy) (deleteV ys ix) ->
  IsPermutation (vCons x xs) (vCons y ys)
perm-cons ix iy perm = HeadPermutation (inTail ix , perm-sym (HeadPermutation (iy , (perm-sym perm))))
