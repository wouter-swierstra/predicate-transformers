{-# OPTIONS --type-in-type #-}
module Recursion where

open import Prelude
open NaturalLemmas
open import Free
open import Maybe
open import Spec

-- Corresponds to the PiG type in \cite{totally-free}
_⇝_ : (I : Set) (O : I → Set) → Set
I ⇝ O = (i : I) → Free I O (O i) -- Mix I O (O i)

-- Perform a recursive call and give the result.
call : ∀ {I O} → (i : I) → Free I O (O i)
call x = Step x Pure

fusc : Nat ⇝ const Nat
fusc Zero = Pure Zero
fusc (Succ i) = Step i λ fn → Step fn λ ffn → Pure (Succ ffn)

-- Replace the recursive calls with calls to f.
-- Note that f can still contain recursive calls (to itself),
-- so we might want to use repeat.
fill-in : ∀ {I O a} → (f : I ⇝ O) → Free I O a → Free I O a
fill-in f (Pure x) = Pure x
fill-in f (Step c k) = f c >>= k
--fill-in f (Spec pre post k) = Spec pre post λ x → fill-in f (k x)

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

more-petrol : ∀ {I O a} (f : I ⇝ O) (m n : Nat) (P : a → Set) (p : Free I O a) →
  (m ≥ n) → petrol f n P p → petrol f m P p
more-petrol f m .0 P (Pure x) z≤n x₁ = x₁
more-petrol f m .0 P (Step c k) z≤n ()
more-petrol f .(suc _) .(suc _) P (Pure x₂) (s≤s x) x₁ = x₁
more-petrol f .(suc _) .(suc _) P (Step c k) (s≤s x) x₁ = more-petrol f _ _ P (f c >>= k) x x₁

plus-petrol : ∀ {I O a} (f : I ⇝ O) (m n : Nat) (P : a → Set) (p : Free I O a) →
  petrol f n P p → petrol f (m + n) P p
plus-petrol f zero n P p x = x
plus-petrol f (suc m) n P p x = add-petrol f (m + n) P p (plus-petrol f m n P p x)

-- The precondition that specifies we terminate
-- (in terms of petrol': that we terminate within n steps).
terminates-in : ∀ {I O a} (f : I ⇝ O) → Free I O a → Nat → Set
terminates-in f p n = petrol f n (const ⊤) p
terminates : ∀ {I O a} (f : I ⇝ O) → Free I O a → Set
terminates f p = Sigma Nat (terminates-in f p)
terminates' : ∀ {I O} (f : I ⇝ O) → I → Set
terminates' f i = terminates f (f i)

-- If a function terminates on an input value, we can compute the output value.
compute : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) → terminates f p → a
compute f (Pure x) t = x
compute f (Step c k) (zero , ())
compute f (Step c k) (suc fst , snd) = compute f (f c >>= k) (fst , snd)
compute' : ∀ {I O} (f : I ⇝ O) (i : I) → terminates' f i → O i
compute' f i t = compute f (f i) t

-- Record which arguments are given to f.
trace : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n : Nat) → List I
trace _ _ Zero = Nil
trace f (Pure _) (Succ n) = Nil
trace f (Step c k) (Succ n) = c :: trace f (f c >>= k) n
-- Take the n'th value of trace.
trace-at : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n : Nat) → Maybe I
trace-at f (Pure x) _ = Nothing
trace-at f (Step c k) Zero = Just c
trace-at f (Step c k) (Succ n) = trace-at f (f c >>= k) n

data InOrder {a : Set} (R : a → a → Set) : (xs : List a) → Set where
  Empty : InOrder R Nil
  Singleton : {i : a} → InOrder R (i :: Nil)
  _:R:_ : ∀ {i j} {xs : List a} → R i j → InOrder R (j :: xs) → InOrder R (i :: (j :: xs))

-- Use the function l as a key to compare on.
keyed : ∀ {I} → (l : I → Nat) → I → I → Set
keyed l i j = l i > l j

descending-step : ∀ {I O a} (l : I → Nat) (f : I ⇝ O) (n : Nat) (c : I) (k : O c → Free I O a) →
  (n > l c) → InOrder (keyed l) (Cons c (trace f (f c >>= k) (Succ (l c)))) → a
descending-step {O} {a} l f n c k n>c desc with f c >>= k
descending-step {O} {a} l f n c k n>c desc | Pure x = x
descending-step {O} {a} l f zero c k () desc | Step c' k'
descending-step {O} {a} l f (suc n) c k n>c (c>c' :R: desc) | Step c' k' with l c
descending-step {I} {O} l f (suc n) c k n>c (() :R: desc) | Step c' k' | zero
descending-step {I} {O} l f (suc n) c k n>c (c>c' :R: desc) | Step c' k' | suc lc = descending-step l f n c' k' (≤-trans c>c' (≤-pred n>c))
  (coerce (cong (InOrder (keyed l) ∘ Cons c') (trace-chop f (f c' >>= k') (suc lc) (suc (l c')) c>c'))
    (desc-cons-chop (suc (l c')) c' (trace f ((f c') >>= k') (suc lc)) desc))
    where
    -- When we go into recursion on the descending list, we chop off some elements.
    chop : ∀ {a} → Nat → List a → List a
    chop Zero _ = Nil
    chop (Succ n) Nil = Nil
    chop (Succ n) (x :: xs) = x :: chop n xs

    desc-cons-chop : ∀ {a R} (n : Nat) (x : a) (xs : List a) → InOrder R (Cons x xs) → InOrder R (Cons x (chop n xs))
    desc-cons-chop zero x xs desc = Singleton
    desc-cons-chop (suc n) x Nil desc = desc
    desc-cons-chop (suc n) x (y :: ys) (x>y :R: desc) = x>y :R: desc-cons-chop n y ys desc

    -- If we chop the trace after it is finished, then this gives the same result.
    trace-chop : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n n' : Nat) → n ≥ n' → chop n' (trace f p n) == trace f p n'
    trace-chop f p n .0 z≤n = refl
    trace-chop f (Pure _) .(suc _) .(suc _) (s≤s x) = refl
    trace-chop f (Step c k) (Succ n) (Succ n') (s≤s x) = cong (Cons c) (trace-chop f (f c >>= k) n n' x)


descending : ∀ {I O a} (l : I → Nat) (f : I ⇝ O) (p : Free I O a) →
  ((n : Nat) → InOrder (keyed l) (trace f p n)) → a
descending l f (Pure x) desc = x
descending l f (Step c k) desc = descending-step l f (suc (l c)) c k ≤-refl (desc (suc (suc (l c))))

descending' : ∀ {I O} (l : I → Nat) (f : I ⇝ O) (i : I) →
  ((n : Nat) → InOrder (keyed l) (Cons i (trace f (f i) n))) → O i
descending' l f i desc = descending l f (f i) (λ n → desc-uncons i _ (desc n))
  where
  desc-uncons : ∀ {a R} (x : a) (xs : List a) → InOrder R (x :: xs) → InOrder R xs
  desc-uncons x .Nil Singleton = Empty
  desc-uncons x .(_ :: _) (x₁ :R: desc) = desc

-- In general, the continuation in p can call f with arbitrarily large arguments if the returned values are arbitrarily large.
-- This does not happen in quicksort: there the recursive calls at each level do not depend on the returned value.
-- (It has the form λ i → Step (r₁ i) λ o₁ → Step (r₂ i) λ o₂ → Pure (f o₁ o₂)).
-- This means we might want to implement descending-step again for this double recursion,
-- or get the correct map for quicksort.

-- Now we will look into proving partial correctness of programs,
-- so we want to prove 'if f terminates on c, then it satisfies ...'.
-- It turns out we already have the type of such specifications:
-- it is exactly `PTs I O', which we used for specifying general effects.
partial-expr : ∀ {I O a} (f-spec : PTs I O) → Free I O a → (a → Set) → Set
partial-expr f-spec (Pure x) P = P x
partial-expr f-spec (Step c k) P = f-spec c (λ x → partial-expr f-spec (k x) P)

-- We can derive a predicate transformer from a relation between input and output values.
pt : ∀ {I O} (R : (i : I) → O i → Set) → PTs I O
pt R i P = ∀ o → R i o → P o
-- Partial correctness means that evaluating one step along f
-- preserves the correctness of the predicate.
partial-correctness : ∀ {I O} (s : PTs I O) → (f : I ⇝ O) → I → Set
partial-correctness s f i = ∀ P → s i P → partial-expr s (f i) P

-- Partial correctness plus termination implies total correctness.
-- However, we need both correctness of the function for all arguments,
-- and for the expression that we are substituting the expression into.
correctness : ∀ {I O a} →
  (s : PTs I O) (cS : ∀ c P P' → (∀ x → P x → P' x) → s c P → s c P') →
  (f : I ⇝ O) (p : Free I O a) (P : a → Set) → ((i : I) → partial-correctness s f i) → partial-expr s p P → (t : terminates f p) → P (compute f p t)
correctness s cS f (Pure x) P p-f p-p t = p-p
correctness s cS f (Step c k) P p-f p-p (zero , ())
correctness s cS f (Step c k) P p-f p-p (suc fst , snd) = correctness s cS f (f c >>= k) P p-f (bind-nested-partial s cS (f c) k P (p-f c _ p-p)) (fst , snd)
  where
  bind-nested-partial : ∀ {I O a b}
    (s : PTs I O) (cS : ∀ c P P' → (∀ x → P x → P' x) → s c P → s c P') →
    (p : Free I O a) (k : a → Free I O b) (P : b → Set) →
    partial-expr s p (λ x → partial-expr s (k x) P) →
    partial-expr s (p >>= k) P
  bind-nested-partial s cS (Pure x) k P p-p-k = p-p-k
  bind-nested-partial s cS (Step c' k') k P p-p-k = cS c' _ _ (λ x → bind-nested-partial s cS (k' x) k P) p-p-k

-- Correctness for functions: if a function is partially correct on all arguments,
-- and it terminates on the given argument,
-- then it terminates with a correct answer.
-- (We need partial correctness on all arguments to carry the proof through the recursive calls.)
correctness' : ∀ {I O} →
  (s : PTs I O) (cS : ∀ c P P' → (∀ x → P x → P' x) → s c P → s c P') →
  (f : I ⇝ O) (i : I) →
  ((i : I) → partial-correctness s f i) → (t : terminates' f i) →
  (P : O i → Set) → s i P → P (compute' f i t)
correctness' s cS f i x t P pt = correctness s cS f (f i) P x (x i P pt) t
