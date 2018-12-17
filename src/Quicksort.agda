module Quicksort where

open import Prelude
open import Data.Nat
open NaturalLemmas
open import Free
open import Recursion
open import Vector

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
     Step zs λ zs' → Pure (ys' ++ (Cons x Nil ++ zs'))

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
run-quicksort' xss = descending' (sum length) quicksort' xss (lemma xss)
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

data Deleted {a : Set} : (x : a) (xs xs' : List a) → Set where
  delHead : ∀ x xs → Deleted x (x :: xs) xs
  delTail : ∀ x x' xs xs' → Deleted x xs xs' → Deleted x (x' :: xs) (x' :: xs')

del-in : ∀ {a x} (xs xs' : List a) → Deleted x xs xs' → x ∈ xs
del-in .(x :: xs') xs' (delHead x .xs') = ∈Head
del-in .(x' :: xs) .(x' :: xs') (delTail x x' xs xs' x₁) = ∈Tail (del-in xs xs' x₁)
in-del : ∀ {a x x'} (xs xs' : List a) → Deleted x xs xs' → x' ∈ xs' → x' ∈ xs
in-del .(x :: xs') xs' (delHead x .xs') x'∈xs' = ∈Tail x'∈xs'
in-del .(x' :: xs) .(x' :: xs') (delTail x x' xs xs' del) ∈Head = ∈Head
in-del .(x' :: xs) .(x' :: xs') (delTail x x' xs xs' del) (∈Tail x'∈xs') = ∈Tail (in-del xs xs' del x'∈xs')

del-++-l : ∀ {a} (x : a) (xs ys zs : List a) → Deleted x ys zs → Deleted x (xs ++ ys) (xs ++ zs)
del-++-l x Nil ys zs x₁ = x₁
del-++-l x (x₂ :: xs) ys zs x₁ = delTail x x₂ (xs ++ ys) (xs ++ zs) (del-++-l x xs ys zs x₁)
del-++-r : ∀ {a} (x : a) (xs ys zs : List a) → Deleted x xs ys → Deleted x (xs ++ zs) (ys ++ zs)
del-++-r x .(x :: ys) ys zs (delHead .x .ys) = delHead x (ys ++ zs)
del-++-r x .(x' :: xs) .(x' :: xs') zs (delTail .x x' xs xs' x₁) = delTail x x' (xs ++ zs) (xs' ++ zs) (del-++-r x xs xs' zs x₁)

data Permutation {a : Set} : (xs ys : List a) → Set where
  Nil : Permutation Nil Nil
  PCons : ∀ x xs xs' ys ys' → Permutation xs' ys' → Deleted x xs xs' → Deleted x ys ys' → Permutation xs ys

sorted : (xs : List Nat) → (xs' : List Nat) → Set
sorted xs xs' = Pair (Permutation xs xs') (InOrder (_<_) xs')

inOrder-++ : ∀ {a R x} (xs ys : List a) → InOrder R xs → InOrder R ys → (∀ x' → x' ∈ xs → R x' x) → (∀ x' → x' ∈ ys → R x x') → InOrder R (xs ++ (x :: ys))
inOrder-++ Nil Nil xs<x x<ys order-xs order-ys = Singleton
inOrder-++ Nil (y :: ys) xs<x x<ys order-xs order-ys = order-ys y ∈Head :R: x<ys
inOrder-++ (x :: Nil) ys xs<x x<ys order-xs order-ys = order-xs x ∈Head :R: inOrder-++ Nil ys Empty x<ys (λ _ ()) order-ys
inOrder-++ (x :: x' :: xs) ys (x₂ :R: xs<x) x<ys order-xs order-ys = x₂ :R: (inOrder-++ (x' :: xs) ys xs<x x<ys (λ x'' z → order-xs x'' (∈Tail z)) order-ys)

-- If a predicate holds for everything in an unpermuted list, it also holds for everything in a permuted list.
perm-in : ∀ {a xs ys} → Permutation xs ys → (x : a) → x ∈ ys → x ∈ xs
perm-in Nil x ()
perm-in (PCons x₁ xs xs' ys ys' perm x₂ x₃) x x∈ys = {!!}
perm-pred : ∀ {a xs xs'} → (P : a → Set) → Permutation xs xs' → (∀ x → x ∈ xs → P x) → (∀ x → x ∈ xs' → P x)
perm-pred P perm all-xs x x∈xs' = all-xs x (perm-in perm x x∈xs')

-- If we filter and then throw away the proof, we can still find the proof by filtering again.
filter'-pred : ∀ {a} xs → (P : a → Set) (p : (x : a) → Dec (P x)) → (x : a) → x ∈ fmap Sigma.fst (filter' p xs) → P x
filter'-pred Nil P p x ()
filter'-pred (x' :: xs) P p x x∈ys with p x'
filter'-pred (x' :: xs) P p .x' ∈Head | yes p₁ = p₁
filter'-pred (x' :: xs) P p x (∈Tail x∈ys) | yes p₁ = filter'-pred xs P p x x∈ys
filter'-pred (x' :: xs) P p x x∈ys | no ¬p = filter'-pred xs P p x x∈ys

perm-++ : ∀ {a} (ys ys' zs zs' : List a) → Permutation ys ys' → Permutation zs zs' → Permutation (ys ++ zs) (ys' ++ zs')
perm-++ .Nil .Nil zs zs' Nil pzs = pzs
perm-++ ys ys' zs zs' (PCons x .ys xs' .ys' ys'' pys x₁ x₂) pzs = PCons x (ys ++ zs) (xs' ++ zs) (ys' ++ zs') (ys'' ++ zs') (perm-++ xs' ys'' zs zs' pys pzs) (del-++-r x ys xs' zs x₁) (del-++-r x ys' ys'' zs' x₂)

perm-filter-< : ∀ x (xs ys zs : List Nat) → Permutation (fmap Sigma.fst (filter' (_lt x) xs)) ys → Permutation (fmap Sigma.fst (filter' (x lt_) xs)) zs → Permutation xs (ys ++ zs)
perm-filter-< = {!!}

qs-sorts : ∀ xs → partial-correctness sorted quicksort xs
qs-sorts Nil = Nil , Empty
qs-sorts (x :: xs) ys' (perm-ys , sort-ys) zs' (perm-zs , sort-zs) = PCons x (x :: xs) xs (ys' ++ Cons x zs') (ys' ++ zs')
  (perm-filter-< x xs ys' zs' perm-ys perm-zs) (delHead x xs) (del-++-l x ys' (Cons x zs') zs' (delHead x zs')) ,
  inOrder-++ ys' zs' sort-ys sort-zs
    (perm-pred (_< x) perm-ys λ x' x'∈ys → filter'-pred xs (_< x) (_lt x) x' x'∈ys)
    (perm-pred (x <_) perm-zs λ x' x'∈zs → filter'-pred xs (x <_) (x lt_) x' x'∈zs)
