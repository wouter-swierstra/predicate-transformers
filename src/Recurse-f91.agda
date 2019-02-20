{-# OPTIONS --type-in-type #-}
module Recurse-f91 where

open import Prelude
open import Free
open import Recursion

open import Data.Nat
open NaturalLemmas
_-_ = _∸_

f91 : Nat ⇝ (const Nat)
f91 i with 100 lt i
f91 i | yes _ = Pure (i - 10)
f91 i | no _ = call (i + 11) >>= call

-- f91-terminates : (n : Nat) → Nat
-- f91-terminates n = descending' (λ i → 101 - i) f91 n λ n₁ → lemma n n₁
--   where
--   lemma : ∀ i n → InOrder (λ i j → (101 ∸ j) < 101 ∸ i) (i :: trace f91 (f91 i) n)
--   lemma i zero = Singleton
--   lemma i (suc n) with 100 lt i
--   lemma i (suc n) | yes p = Singleton
--   lemma i (suc n) | no ¬p = {!!} :R: {!!} -- TODO: what should be the second argument?

f91-spec : Nat → Nat → Set
f91-spec i o with 100 lt i
f91-spec i o | yes _ = o == i - 10
f91-spec i o | no _ = o == 91

f91-proof : (n : Nat) → partial-correctness (pt f91-spec) f91 n
f91-proof n P pf with 100 lt n
f91-proof n P pf | yes p = pf (n ∸ 10) refl
f91-proof n P pf | no ¬p = λ o z o₁ z₁ → pf o₁ (lemma n ¬p o z o₁ z₁)
  where
  plusminus : ∀ n k → n + Succ k ∸ k == Succ n
  plusminus zero zero = refl
  plusminus zero (suc k) = plusminus zero k
  plusminus (suc n) zero = cong suc (plusminus n zero)
  plusminus (suc n) (suc k) = trans (cong (_∸ k) (+-succ n (suc k))) (plusminus (suc n) k)

  exactly : (a b : Nat) → ¬ (Succ b ≤ a) → (Succ b ≤ Succ a) → a == b
  exactly zero .0 x (s≤s z≤n) = refl
  exactly (suc a) zero x (s≤s x₁) = magic (x (s≤s z≤n))
  exactly (suc a) (suc b) x (s≤s x₁) = cong suc (exactly a b (λ z → x (s≤s z)) x₁)

  lemma' : ∀ n → (101 ≤ n → ⊥) → 101 ≤ Succ n → n ≡ 100
  lemma' n x x₁ = exactly n 100 x x₁

  lemma : ∀ n → (101 ≤ n → ⊥) → ∀ o → f91-spec (n + 11) o → ∀ o₁ → f91-spec o o₁ → o₁ ≡ 91
  lemma n x o x₁ o₁ x₂ with 100 lt (n + 11)
  lemma n x .91 refl .91 refl | no ¬p = refl -- We terminate in one step...
  lemma n x .(n + 11 ∸ 10) refl o₁ x₂ | yes p with 100 lt (n + 11 ∸ 10)
  lemma n x .(n + _ ∸ suc _) refl .91 refl | yes p | no ¬p = refl -- Or in two steps...
  lemma n x .(n + _ ∸ suc _) refl .(n + 11 ∸ 10 ∸ 10) refl | yes p | yes p₁ = trans (cong (_∸ 10) (plusminus n 10)) (cong (_∸ 9) (lemma' n x (=-≤-= refl p₁ (plusminus n 10)))) -- Or after recursing on n
