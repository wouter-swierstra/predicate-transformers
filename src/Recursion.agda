{-# OPTIONS --type-in-type #-}
module Recursion where

open import Prelude
open import Free
open import Spec
open import Vector

-- Corresponds to the PiG type in \cite{totally-free}
_⇝_ : (I : Set) (O : I → Set) → Set
I ⇝ O = (i : I) → Free I O (O i) -- Mix I O (O i)

fusc : Nat ⇝ const Nat
fusc Zero = Pure Zero
fusc (Succ i) = Step i λ fn → Step fn λ ffn → Pure (Succ ffn)

open import Maybe

-- Replace the recursive calls with calls to f.
-- Note that f can still contain recursive calls (to itself),
-- so we might want to use repeat.
fill-in : ∀ {I O a} → (f : I ⇝ O) → Free I O a → Free I O a
fill-in f (Pure x) = Pure x
fill-in f (Step c k) = f c >>= k
--fill-in f (Spec pre post k) = Spec pre post λ x → fill-in f (k x)

repeat : ∀ {a} → Nat → (a → a) → a → a
repeat Zero = id
repeat (Succ n) f = repeat n f ∘ f

-- Does the program terminate in n calls to f and then satisfy the predicate?
-- (Here, all calls in f are also calls to f)
petrol : ∀ {I O a} → (f : I ⇝ O) → Nat → (a → Set) → Free I O a → Set
petrol f n P (Pure x) = P x
petrol f Zero P (Step c k) = ⊥
petrol f (Succ n) P (Step c k) = petrol f n P (f c >>= k)
--petrol f n P (Spec {a'} pre post k) = Pair pre ((x : a') → post x → petrol f n P (k x))

-- Run f recursively on a given input.
petrol' : ∀ {I O} → (f : I ⇝ O) → Nat → ((i : I) → O i → Set) → I → Set
petrol' f n P i = petrol f n (P i) (f i)

-- Adding more petrol preserves postconditions.
open import Data.Nat.Base
add-petrol : ∀ {I O a} (f : I ⇝ O) (n : Nat) (P : a → Set) (p : Free I O a) →
  petrol f n P p → petrol f (Succ n) P p
add-petrol f n P (Pure x₁) x = x
--add-petrol f n P (Spec x₁ x₂ k) (fst , snd) = fst , (λ x x₃ → add-petrol f n P (k x) (snd x x₃))
add-petrol f zero P (Step c k) ()
add-petrol f (suc n) P (Step c k) x = add-petrol f n P (f c >>= k) x

plus-petrol : ∀ {I O a} (f : I ⇝ O) (m n : Nat) (P : a → Set) (p : Free I O a) →
  petrol f n P p → petrol f (m + n) P p
plus-petrol f zero n P p x = x
plus-petrol f (suc m) n P p x = add-petrol f (m + n) P p (plus-petrol f m n P p x)

-- The precondition that specifies we terminate
-- (in terms of petrol': that we terminate within n steps).
terminates : ∀ {I O a} (f : I ⇝ O) → Free I O a → Set
terminates f p = Sigma Nat (λ n → petrol f n (const ⊤) p)
terminates' : ∀ {I O} (f : I ⇝ O) → I → Set
terminates' f i = terminates f (f i)

data WhenStep {C R a} (P : C → Set) : Free C R a → Set where
  BecausePure : ∀ {x} → WhenStep P (Pure x)
  BecauseStep : ∀ {c k} → P c → WhenStep P (Step c k)

the : (a : Set) → a → a
the _ x = x

in-fin : (c i : Nat) → (c < i) → Fin i
in-fin c zero ()
in-fin zero (suc i) x = F0
in-fin (suc c) (suc i) (s≤s x) = FS (in-fin c i x)

<-suc : (c : Nat) → c < suc c
<-suc zero = s≤s z≤n
<-suc (suc c) = s≤s (<-suc c)

trace : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n : Nat) → List I
trace _ _ Zero = Nil
trace f (Pure _) (Succ n) = Nil
trace f (Step c k) (Succ n) = Cons c (trace f (f c >>= k) n)

chop : ∀ {a} → Nat → List a → List a
chop Zero _ = Nil
chop (Succ n) Nil = Nil
chop (Succ n) (Cons x xs) = Cons x (chop n xs)

trace-chop : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n n' : Nat) → n ≥ n' → chop n' (trace f p n) == trace f p n'
trace-chop f p n .0 z≤n = refl
trace-chop f (Pure _) .(suc _) .(suc _) (s≤s x) = refl
trace-chop f (Step c k) (Succ n) (Succ n') (s≤s x) = cong (Cons c) (trace-chop f (f c >>= k) n n' x)

data Descending {a : Set} (R : a → a → Set) : (xs : List a) → Set where
  Empty : Descending R Nil
  Singleton : {i : a} → Descending R (Cons i Nil)
  Cons : ∀ {i j} {xs : List a} → R i j → Descending R (Cons j xs) → Descending R (Cons i (Cons j xs))

desc-chop : ∀ {a R} (n : Nat) (xs : List a) → Descending R xs → Descending R (chop n xs)
desc-chop zero Nil desc = desc
desc-chop zero (Cons x xs) desc = Empty
desc-chop (suc zero) Nil desc = desc
desc-chop (suc zero) (Cons x Nil) desc = desc
desc-chop (suc zero) (Cons x (Cons x₁ xs)) desc = Singleton
desc-chop (suc (suc n)) Nil desc = desc
desc-chop (suc (suc n)) (Cons x Nil) desc = desc
desc-chop (suc (suc n)) (Cons x (Cons x' xs)) (Cons x<x' desc) = Cons x<x' (desc-chop (suc n) (Cons x' xs) desc)

desc-cons-chop : ∀ {a R} (n : Nat) (x : a) (xs : List a) → Descending R (Cons x xs) → Descending R (Cons x (chop n xs))
desc-cons-chop zero x xs desc = Singleton
desc-cons-chop (suc n) x Nil desc = desc
desc-cons-chop (suc n) x (Cons y ys) (Cons x>y desc) = Cons x>y (desc-cons-chop n y ys desc)

data JustSo {a : Set} (P : a → Set) : Maybe a → Set where
  onJust : {x : a} → P x → JustSo P (Just x)

≤-refl : ∀ {x} → x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc x} = s≤s ≤-refl
≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n x₂ = z≤n
≤-trans (s≤s x₁) (s≤s x₂) = s≤s (≤-trans x₁ x₂)

-- If f calls itself with a strictly smaller number than its argument,
-- any program that calls f recursively will terminate.
-- We use n to show termination of this function.
descending-step : ∀ {O a} (f : Nat ⇝ O) (n : Nat) (c : Nat) (k : O c → Free Nat O a) →
  (n > c) → Descending _>_ (Cons c (trace f (f c >>= k) (Succ c))) → a
descending-step {O} {a} f n c k n>c desc with f c >>= k
descending-step {O} {a} f n c k n>c desc | Pure x = x
descending-step {O} {a} f zero c k () desc | Step c' k'
descending-step {O} {a} f (suc n) zero k n>c (Cons () desc) | Step c' k'
descending-step {O} {a} f (suc n) (suc c) k n>c (Cons c>c' desc) | Step c' k' =
  descending-step f n c' k' (≤-trans c>c' (≤-pred n>c))
  (coerce (cong (Descending _>_ ∘ Cons c') (trace-chop f (f c' >>= k') (suc c) (suc c') c>c'))
    (desc-cons-chop (suc c') c' (trace f ((f c') >>= k') (suc c)) desc))

descending : ∀ {O a} (f : Nat ⇝ O) (p : Free Nat O a) →
  ((n : Nat) → Descending _>_ (trace f p n)) → a
descending f (Pure x) desc = x
descending f (Step c k) desc = descending-step f (suc c) c k ≤-refl (desc (suc (suc c)))

-- TODO: show that we can do the same for any I with a map l : (I → Nat) such that map l (trace ...) is descending
-- (e.g. List a and len : List a → Nat)

