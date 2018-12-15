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
trace f (Step c k) (Succ n) = c :: trace f (f c >>= k) n

_!!?_ : ∀ {a} (xs : List a) (n : Nat) → Maybe a
Nil !!? _ = Nothing
(x :: xs) !!? Zero = Just x
(x :: xs) !!? (Succ n) = xs !!? n

trace-at : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n : Nat) → Maybe I
trace-at f (Pure x) _ = Nothing
trace-at f (Step c k) Zero = Just c
trace-at f (Step c k) (Succ n) = trace-at f (f c >>= k) n

chop : ∀ {a} → Nat → List a → List a
chop Zero _ = Nil
chop (Succ n) Nil = Nil
chop (Succ n) (x :: xs) = x :: chop n xs

trace-chop : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n n' : Nat) → n ≥ n' → chop n' (trace f p n) == trace f p n'
trace-chop f p n .0 z≤n = refl
trace-chop f (Pure _) .(suc _) .(suc _) (s≤s x) = refl
trace-chop f (Step c k) (Succ n) (Succ n') (s≤s x) = cong (Cons c) (trace-chop f (f c >>= k) n n' x)

data InOrder {a : Set} (R : a → a → Set) : (xs : List a) → Set where
  Empty : InOrder R Nil
  Singleton : {i : a} → InOrder R (i :: Nil)
  _:R:_ : ∀ {i j} {xs : List a} → R i j → InOrder R (j :: xs) → InOrder R (i :: (j :: xs))

desc-uncons : ∀ {a R} (x : a) (xs : List a) → InOrder R (x :: xs) → InOrder R xs
desc-uncons x .Nil Singleton = Empty
desc-uncons x .(_ :: _) (x₁ :R: desc) = desc

desc-chop : ∀ {a R} (n : Nat) (xs : List a) → InOrder R xs → InOrder R (chop n xs)
desc-chop zero Nil desc = desc
desc-chop zero (x :: xs) desc = Empty
desc-chop (suc zero) Nil desc = desc
desc-chop (suc zero) (x :: Nil) desc = desc
desc-chop (suc zero) (x :: x₁ :: xs) desc = Singleton
desc-chop (suc (suc n)) Nil desc = desc
desc-chop (suc (suc n)) (x :: Nil) desc = desc
desc-chop (suc (suc n)) (x :: x' :: xs) (x<x' :R: desc) = x<x' :R: desc-chop (suc n) (Cons x' xs) desc

desc-cons-chop : ∀ {a R} (n : Nat) (x : a) (xs : List a) → InOrder R (Cons x xs) → InOrder R (Cons x (chop n xs))
desc-cons-chop zero x xs desc = Singleton
desc-cons-chop (suc n) x Nil desc = desc
desc-cons-chop (suc n) x (y :: ys) (x>y :R: desc) = x>y :R: desc-cons-chop n y ys desc

data JustSo {a : Set} (P : a → Set) : Maybe a → Set where
  onJust : {x : a} → P x → JustSo P (Just x)

≤-refl : ∀ {x} → x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc x} = s≤s ≤-refl
≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n x₂ = z≤n
≤-trans (s≤s x₁) (s≤s x₂) = s≤s (≤-trans x₁ x₂)

{-
-- If f calls itself with a strictly smaller number than its argument,
-- any program that calls f recursively will terminate.
-- We use n to show termination of this function.
descending-step : ∀ {O a} (f : Nat ⇝ O) (n : Nat) (c : Nat) (k : O c → Free Nat O a) →
  (n > c) → InOrder _>_ (Cons c (trace f (f c >>= k) (Succ c))) → a
descending-step {O} {a} f n c k n>c desc with f c >>= k
descending-step {O} {a} f n c k n>c desc | Pure x = x
descending-step {O} {a} f zero c k () desc | Step c' k'
descending-step {O} {a} f (suc n) zero k n>c (Cons () desc) | Step c' k'
descending-step {O} {a} f (suc n) (suc c) k n>c (Cons c>c' desc) | Step c' k' =
  descending-step f n c' k' (≤-trans c>c' (≤-pred n>c))
  (coerce (cong (InOrder _>_ ∘ Cons c') (trace-chop f (f c' >>= k') (suc c) (suc c') c>c'))
    (desc-cons-chop (suc c') c' (trace f ((f c') >>= k') (suc c)) desc))

descending : ∀ {O a} (f : Nat ⇝ O) (p : Free Nat O a) →
  ((n : Nat) → InOrder _>_ (trace f p n)) → a
descending f (Pure x) desc = x
descending f (Step c k) desc = descending-step f (suc c) c k ≤-refl (desc (suc (suc c)))
-}

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

descending : ∀ {I O a} (l : I → Nat) (f : I ⇝ O) (p : Free I O a) →
  ((n : Nat) → InOrder (keyed l) (trace f p n)) → a
descending l f (Pure x) desc = x
descending l f (Step c k) desc = descending-step l f (suc (l c)) c k ≤-refl (desc (suc (suc (l c))))

compute : ∀ {I O} (l : I → Nat) (f : I ⇝ O) (i : I) →
  ((n : Nat) → InOrder (keyed l) (Cons i (trace f (f i) n))) → O i
compute l f i desc = descending l f (f i) (λ n → desc-uncons i _ (desc n))

-- In general, the continuation in p can call f with arbitrarily large arguments if the returned values are arbitrarily large.
-- This does not happen in quicksort: there the recursive calls at each level do not depend on the returned value.
-- (It has the form λ i → Step (r₁ i) λ o₁ → Step (r₂ i) λ o₂ → Pure (f o₁ o₂)).
-- This means we might want to implement descending-step again for this double recursion,
-- or get the correct map for quicksort.

_lt_ : (i j : Nat) → Dec (i < j)
_ lt Zero = no (λ ())
Zero lt Succ j = yes (s≤s z≤n)
Succ i lt Succ j with i lt j
suc i lt suc j | yes x = yes (s≤s x)
suc i lt suc j | no x = no (λ z → x (≤-pred z))

call : ∀ {I O} → (i : I) → Free I O (O i)
call x = Step x Pure

even : Nat → Bool
even 0 = True
even 1 = False
even (Succ (Succ n)) = even n

half : Nat → Nat
half 0 = 0
half 1 = 1
half (Succ (Succ n)) = Succ (half n)

collatz : Nat ⇝ const Nat
collatz 0 = Pure 0
collatz 1 = Pure 1
collatz n@(Succ (Succ _)) =
  if even n
  then call (half n)
  else (call (3 * n + 1))

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
collatz-27 = 112 , tt --{!trace collatz (call 27) 112!}

succ-inj : (i j : Nat) → Succ i == Succ j → i == j
succ-inj i .i refl = refl

eq-Nat : (i j : Nat) → Dec (i == j)
eq-Nat zero zero = yes refl
eq-Nat zero (suc j) = no (λ ())
eq-Nat (suc i) zero = no (λ ())
eq-Nat (suc i) (suc j) with eq-Nat i j
eq-Nat (suc i) (suc j) | yes x = yes (cong suc x)
eq-Nat (suc i) (suc j) | no x = no (λ z → x (succ-inj i j z))

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

double : Nat → Nat
double 0 = 0
double (Succ n) = Succ (Succ (double n))

open import Data.Nat.Divisibility

_eq_ : Nat → Nat → Bool
zero eq zero = True
zero eq suc b = False
suc a eq zero = False
suc a eq suc b = a eq b

-- Which numbers precede the given one in a Collatz sequence?
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

filter' : ∀ {a P} → ((x : a) → Dec (P x)) → List a → List (Sigma a P)
filter' p Nil = Nil
filter' p (x :: xs) with p x
filter' p (x :: xs) | yes px = (x , px) :: filter' p xs
filter' p (x :: xs) | no np = filter' p xs

-- The default definition of quicksort,
-- which doesn't allow us to prove termination using `descending'.
quicksort : List Nat ⇝ λ xs → List Nat -- Sigma (List Nat) λ ys → InOrder _<_ ys
quicksort Nil = Pure Nil -- (Nil , Empty)
quicksort (x :: xs) = let
    ys,lt = filter' (_lt x) xs
    ys = fmap Sigma.fst ys,lt
    zs,gt = filter' (x lt_) xs
    zs = fmap Sigma.fst zs,gt
  in Step ys λ ys' →
     Step zs λ zs' → Pure (ys ++ (Cons x Nil ++ zs))

≤-succ : ∀ {i j} → i ≤ j → i ≤ Succ j
≤-succ z≤n = z≤n
≤-succ (s≤s x) = s≤s (≤-succ x)

filter-shortens : ∀ {a} {P : a → Set} (p : (x : a) → Dec (P x)) (xs : List a) → length xs ≥ length (filter' p xs)
filter-shortens p Nil = z≤n
filter-shortens p (x :: xs) with p x
filter-shortens p (x :: xs) | yes x₁ = s≤s (filter-shortens p xs)
filter-shortens p (x :: xs) | no x₁ = ≤-succ (filter-shortens p xs)

fmap-preserves-length : ∀ {a b} (f : a → b) (xs : List a) → length xs == length (fmap f xs)
fmap-preserves-length f Nil = refl
fmap-preserves-length f (x :: xs) = cong suc (fmap-preserves-length f xs)

antisymm : ∀ x y → x < y → y < x → ⊥
antisymm zero y x₁ ()
antisymm (suc x) zero () x₂
antisymm (suc x) (suc y) (s≤s x₁) (s≤s x₂) = antisymm x y x₁ x₂

+-succ : ∀ a b → a + Succ b == Succ (a + b)
+-succ zero b = refl
+-succ (suc a) b = cong suc (+-succ a b)

=-≤-= : ∀ {i j k l} → i == j → j ≤ k → k == l → i ≤ l
=-≤-= refl x refl = x

filter-<-shortens : ∀ x xs → length xs ≥ length (filter' (_lt x) xs) + length (filter' (x lt_) xs)
filter-<-shortens x Nil = z≤n
filter-<-shortens x (y :: xs) with y lt x
filter-<-shortens x (y :: xs) | yes p with x lt y
filter-<-shortens x (y :: xs) | yes p | yes p₁ = magic (antisymm _ _ p p₁)
filter-<-shortens x (y :: xs) | yes p | no ¬p = s≤s (filter-<-shortens x xs)
filter-<-shortens x (y :: xs) | no ¬p with x lt y
filter-<-shortens x (y :: xs) | no ¬p | yes p = =-≤-= (+-succ (length (filter' (_lt x) xs)) (length (filter' (x lt_) xs))) (s≤s (filter-<-shortens x xs)) refl
filter-<-shortens x (y :: xs) | no ¬p | no ¬p₁ = ≤-succ (filter-<-shortens x xs)

-- The `descending' theorem allows us to prove that singly recursive functions terminate if their arguments can be mapped to a well-order.
-- Now we want to do the same but $f$ can contain an arbitrary number of calls to itself for each argument, let's say $a : I → Nat$ counts this.
-- When we have the definition of $f$, we know that this is finite (because we can count the number of `Step` constructors),
-- but for arbitrary $f$ this is not decidable!
-- That is why we need the argument.
{- -- TODO: implement this correctly...
more-recursion : {o : Set} (f : Nat ⇝ const Nat) (c : Nat) (k : Nat → Free Nat (const Nat) o) →
  (a : Nat → Nat) → (∀ c → (∀ c' → c' < c → terminates-in f (f c') (a c')) → terminates-in f (f c) (a c)) →
  (∀ c c' → c' < c → a c' < a c) →
  (b : Nat → Nat) → (terminates-in f (f c) (a c) → terminates-in f (f c >>= k) (b c)) →
  (n : Nat) → n > a c →
  (∀ c → all' (_< c) (trace f (f c) n)) →
  terminates-in f (f c >>= k) (a c)
more-recursion f c k a f-breadth a-desc b k-depth zero () desc
more-recursion f c k a f-breadth a-desc b k-depth (suc n) n>ac desc with desc c
... | dc with f c >>= k
more-recursion f c k a f-breadth a-desc b k-depth (suc n) n>ac desc | dc | Pure x = {!!}
more-recursion f c k a f-breadth a-desc b k-depth (suc n) n>ac desc | dc | Step c' k' = {!!} -- FIXME: why isn't f c >>= k replaced by Step c' k' in the goal?
{-
more-recursion f c@(suc c-1) k a f-breadth a-desc b k-depth (suc n) (s≤s n>ac) desc | (s≤s c'≤c-1 , _) | Step c' k' with a-desc c c' {!!}
... | ac-1<ac with a c
more-recursion f (suc c-1) k a f-breadth a-desc b k-depth (suc n) (s≤s n>ac) desc | (s≤s c'≤c-1 , _) | Step c' k' | () | zero
more-recursion f (suc c-1) k a f-breadth a-desc b k-depth (suc n) (s≤s n>ac) desc | (s≤s c'≤c-1 , _) | Step c' k' | s≤s ac'<ac | suc ac = more-petrol f ac (a c') (const ⊤) (f c' >>= k') ac'<ac (more-recursion f c' k' a f-breadth a-desc {!!} {!!} n (≤-trans (s≤s ac'<ac) n>ac) {!!})
-- {!more-recursion f c' k' a f-breadth a-desc (λ c'' → b c'')!}
-- more-recursion f c' k' a f-breadth a-desc (λ c'' → Succ (b c'')) (λ x → more-petrol f _ {!!} (const ⊤) (f c' >>= k') {!!} {!!}) n (≤-trans (a-desc (suc c-1) c' (s≤s c'≤c-1)) n>ac) {!!}
-}
-}

quicksort-terminates : (xs : List Nat) → terminates' quicksort xs
quicksort-terminates xs = {!!}

uncons : ∀ {a n} → Vec (Succ n) a → Pair a (Vec n a)
uncons (x :: xs) = x , xs

-- Extract the final step of quicksort so we can use it in the proof it terminates.
assemble : ∀ {n} (x : Nat) → Vec (suc (suc n)) (List Nat) → Vec (suc n) (List Nat)
assemble x (ys :: zs :: xss) = (ys ++ (x :: zs)) :: xss

-- If we convert quicksort to single recursion, where we guarantee it sorts all lists in the vector,
-- then we might be able to prove termination since the sum of all lengths strictly decreases.
quicksort' : List (List Nat) ⇝ λ xss → Vec (length xss) (List Nat) -- Sigma (List Nat) λ ys → InOrder _<_ ys
quicksort' Nil = Pure vNil
quicksort' (Nil :: xss) = quicksort' xss >>= λ xss' → Pure (Nil :: xss') -- Note that we can use structural recursion here, and it makes for a neater termination proof, so we do that (for now).
quicksort' ((x :: xs) :: xss) = let
    ys,lt = filter' (_lt x) xs
    ys = fmap Sigma.fst ys,lt
    zs,gt = filter' (x lt_) xs
    zs = fmap Sigma.fst zs,gt
  in Step (ys :: zs :: xss) λ ys'::zs'::xss' → Pure (assemble x ys'::zs'::xss')

sum : ∀ {a} (f : a → Nat) (xs : List a) → Nat
sum f Nil = 0
sum f (x :: xs) = f x + sum f xs

+-assoc : ∀ a b c → a + (b + c) == (a + b) + c
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

≤-+ : ∀ {a b} c → a ≤ b → a + c ≤ b + c
≤-+ {zero} {zero} c x = ≤-refl
≤-+ {zero} {suc b} c x = ≤-succ (≤-+ {zero} {b} c z≤n)
≤-+ {suc a} {zero} c ()
≤-+ {suc a} {suc b} c (s≤s x) = s≤s (≤-+ c x)

bind-assoc : ∀ {I O a b c} (p : Free I O a) (f : a → Free I O b) (g : b → Free I O c) →
  (p >>= f) >>= g == p >>= (λ x → f x >>= g)
bind-assoc (Pure x) f g = refl
bind-assoc (Step c k) f g = cong (Step c) (extensionality (λ x → bind-assoc (k x) f g))

-- fmap doesn't add anything to the trace.
trace-fmap : ∀ {I O a b} f (p : Free I O a) (g : a → b) n → trace f p n == trace f (p >>= λ x → Pure (g x)) n
trace-fmap f p g zero = refl
trace-fmap f (Pure x) g (suc n) = refl
trace-fmap f (Step c k) g (suc n) = cong (c ::_) (trans (trace-fmap f (f c >>= k) g n) (cong (λ p → trace f p n) (bind-assoc (f c) k (Pure ∘ g))))

desc-≤ : ∀ {a} x y xs → (l : a → Nat) → l x ≤ l y → InOrder (keyed l) (x :: xs) → InOrder (keyed l) (y :: xs)
desc-≤ x y .Nil l x≤y Singleton = Singleton
desc-≤ x y .(_ :: _) l x≤y (x>x' :R: io) = (≤-trans x>x' x≤y) :R: io

run-quicksort' : (xss : List (List Nat)) → Vec (length xss) (List Nat)
run-quicksort' xss = compute (sum length) quicksort' xss (lemma xss)
  where
  lemma : ∀ xss n →
    InOrder (λ i j → suc (sum length j) ≤ sum length i)
    (xss :: trace quicksort' (quicksort' xss) n)
  lemma xss zero = Singleton
  lemma Nil (suc n) = Singleton
  lemma (Nil :: xss) (suc n) = coerce (cong (λ ts → InOrder (keyed (sum length)) ((Nil :: xss) :: ts)) (trace-fmap quicksort' (quicksort' xss) (Nil ::_) (suc n)))
    (desc-≤ xss (Nil :: xss) (trace quicksort' (quicksort' xss) (suc n)) (sum length) ≤-refl
      (lemma xss (suc n)))
  lemma ((x :: xs) :: xss) (suc n) = let
      ys,lt = filter' (_lt x) xs
      ys = fmap Sigma.fst ys,lt
      zs,gt = filter' (x lt_) xs
      zs = fmap Sigma.fst zs,gt
    in s≤s (=-≤-= (trans (trans
        (cong (λ lys → lys + (length zs + sum length xss)) (sym (fmap-preserves-length Sigma.fst ys,lt)))
        (cong (λ lzs → length ys,lt + (lzs + sum length xss)) (sym (fmap-preserves-length Sigma.fst zs,gt))))
        (+-assoc (length ys,lt) (length zs,gt) (sum length xss)))
      (≤-+ (sum length xss) (filter-<-shortens x xs))
      refl) :R: coerce (cong (λ ts → InOrder (keyed (sum length)) (((ys :: zs :: xss) :: ts))) (trace-fmap quicksort' (quicksort' (ys :: zs :: xss)) (assemble x) n)) (lemma (ys :: zs :: xss) n)

run-quicksort : List Nat → List Nat
run-quicksort xs with run-quicksort' (xs :: Nil)
... | xs' :: vNil = xs'

data Frame (I : Set) (O : I → Set) : Set where
  frame : {a : Set} → (c : I) → (O c → Free I O a) → Frame I O
stack : ∀ I O → Set
stack I O = List (Frame I O)

-- Give the call stack after doing one calculation step.
next-stack : ∀ {I O} (f : I ⇝ O) → stack I O → stack I O
next-stack f Nil = Nil
next-stack f ((frame c' k') :: cs) with f c' >>= k'
next-stack f ((frame c' k') :: cs) | Pure x = cs
next-stack f ((frame c' k') :: cs) | Step c k = frame c k :: cs
-- Give the call stack after n calculation steps.
trace-stack : ∀ {I O a} (f : I ⇝ O) (p : Free I O a) (n : Nat) → stack I O
trace-stack f (Pure x) zero = Nil
trace-stack f (Step c k) zero = frame c k :: Nil
trace-stack f p (suc n) = next-stack f (trace-stack f p n)

bla = {! trace-stack quicksort (call (0 :: 3 :: 2 :: 4 :: Nil)) 100 !}
