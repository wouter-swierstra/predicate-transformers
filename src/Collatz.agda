{-# OPTIONS --type-in-type #-}
module Collatz where

open import Prelude
open import Data.Nat
open NaturalLemmas
open import Free
open import Recursion

-- Example: collatz sequence.
open NumberTheory
collatz : Nat ⇝ const Nat
collatz 0 = Pure 0
collatz 1 = Pure 1
collatz n@(Succ (Succ _)) =
  if even n
  then call (half n)
  else (call (3 * n + 1))

-- For many examples, we can show it terminates (even after hundreds of steps).
collatz-2 : terminates' collatz 2
collatz-2 = 1 , tt
collatz-3 : terminates' collatz 3
collatz-3 = 7 , tt
collatz-4 : terminates' collatz 4
collatz-4 = 2 , tt
collatz-5 : terminates' collatz 5
collatz-5 = 5 , tt
collatz-7 : terminates' collatz 7
collatz-7 = 16 , tt
collatz-9 : terminates' collatz 9
collatz-9 = 19 , tt
collatz-11 : terminates' collatz 11
collatz-11 = 14 , tt
collatz-27 : terminates' collatz 27
collatz-27 = 112 , tt

-- Another collatz function: give the collatz sequence for `n' until we hit `s'.
collatz-until : Nat → Nat ⇝ const Nat
collatz-until s n with eq-Nat s n
... | yes eq = Pure s
... | no ne =
  if even n
  then call (half n)
  else (call (3 * n + 1))

search : (x : Nat) (xs : List Nat) → Dec (x ∈ xs)
search x Nil = no (λ ())
search x (x' :: xs) with eq-Nat x x'
search x (.x :: xs) | yes refl = yes ∈Head
search x (x' :: xs) | no ne with search x xs
search x (x' :: xs) | no ne | yes x∈xs = yes (∈Tail x∈xs)
search x (x' :: xs) | no ne | no x∉xs = no (headNorTail ne x∉xs)
  where
  headNorTail : ¬ (x == x') → ¬ (x ∈ xs) → ¬ (x ∈ Cons x' xs)
  headNorTail ne ∉ ∈Head = ne refl
  headNorTail ne ∉ (∈Tail i) = ∉ i

-- Which numbers precede the given one in a Collatz sequence?
open import Data.Nat.Divisibility
collatz-pred : Nat → List Nat
collatz-pred 0 = Nil
collatz-pred x@(Succ x-1) = (
  if' 3 ∣? x-1
  then (λ div →
    if (quotient div eq 1) || even (quotient div) -- Make sure we don't repeat numbers.
    then id
    else (quotient div ::_))
  else λ ndiv → id) (double x :: Nil)

inverse-collatz : List Nat ⇝ (λ _ → List Nat)
inverse-collatz xs = call (xs >>= collatz-pred)

-- In the n'th recursive step, inverse-collatz' contains all numbers such that collatz n terminates in n steps.
inverse-collatz' = inverse-collatz (Cons 0 (Cons 1 Nil))
