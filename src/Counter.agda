{-# OPTIONS --type-in-type #-}
module Counter where

open import Prelude hiding (_⟨_⟩_)
open import Preorder
open import MonadSpec

State : Set → Set → Set
State s a = s → Pair a s

instance
  IsMonad-State : {s : Set} → IsMonad (State s)
  IsMonad-State {s} = isMonad bind' _,_
    where
    bind' : {a b : Set} → State s a → (a → State s b) → State s b
    bind' mx f t = uncurry f (mx t)

Pre' = Pre (State Nat)
Post' = Post (State Nat)

data C : Set where
  Tick : C
R : C -> Set
R Tick = ⊤
Count = Mix C R (State Nat)

tick : Count ⊤
tick = Step Tick Pure
tickAfter : {a : Set} → State Nat a → State Nat a
tickAfter mx n = Pair.fst (mx n) , Succ (Pair.snd (mx n))

-- Define the predicate transformer.
-- Although the only operations are to leave the counter alone
-- or increment it,
-- we need to ensure incrementing happens after running.
ptCount : (c : C) → (R c → Pre') → Pre'
ptCount Tick P mx = P tt (tickAfter mx)

pt-implies : (c : C) → {P P' : R c → Pre (State Nat)} → ((x : R c) (i : State Nat ⊤) → P x i → P' x i) → (i : State Nat ⊤) → ptCount c P i → ptCount c P' i
pt-implies Tick x mx x₁ = x tt (tickAfter mx) x₁

Semantics-Count : Semantics C R (State Nat)
Semantics-Count = semantics ptCount handler pt-implies lifter-bind
  where
  handler : (c : C) → State Nat (R c)
  handler Tick = tickAfter (pure tt)
  lifter-bind : {a : Set} (P : Post (State Nat) a) (c : C)
    (k : R c → State Nat a) (i : State Nat ⊤) →
    ptCount c (λ r o → P (o >> k r)) i ⇔ P (i >> handler c >>= k)
  lifter-bind P Tick k i with k tt
  ... | mx = ⇔-refl

pointwise : {a : Set} → (Q : Nat → a → Nat → Set) → State Nat a → Set
pointwise Q mx = (i : Nat) → (Q i) (Pair.fst (mx i)) (Pair.snd (mx i))

data OnPred {a : Set} (P : State Nat a → Set) : State Nat a → Set where
  onPred : {mx : State Nat a} → P mx → OnPred P (tickAfter mx)

doTick : {P : Pre'} {Q : Post' ⊤} ->
  Impl ptCount (spec (OnPred P) Q) ->
  Impl ptCount (spec P Q)
doTick (impl prog code (refine proof)) = impl
  (tick >>= (λ _ → prog))
  (λ r → code)
  (refine λ i R x → proof (tickAfter i) R (onPred (Pair.fst x) , Pair.snd x))

rep : {m : Set → Set} {{M : IsMonad m}} → Nat -> m ⊤ -> m ⊤
rep Zero m = pure tt
rep (Succ n) m = m >>= \_ -> rep n m

hanoi : Nat -> Count ⊤
hanoi Zero = pure tt
hanoi (Succ n) = hanoi n >>= \_ -> tick >>= \_ -> hanoi n

open import Data.Nat.Base
open NaturalLemmas
-- Sum of the first $n$ powers of $2$: $2^n - 1$.
binsum : Nat -> Nat
binsum Zero = 0
binsum (Succ n) = 1 + (binsum n + binsum n)

hanoiSpec : Nat -> Count ⊤
hanoiSpec n = spec (λ mx → ⊤) (pointwise λ i _ o → o == i + binsum n)

hanoiImpl : (n : Nat) -> Impl ptCount (hanoiSpec n)
hanoiImpl Zero = doReturn' tt λ i x i₁ → trans {!!} (plus-zero i₁)
hanoiImpl (Succ n) = doBind pt-implies (hanoiImpl n) λ _ →
  doTick (
  doSharpen (λ i x → {!!}) {!!} (
  doBind pt-implies (hanoiImpl n) \_ ->
  doReturn tt ))
  where
  {-
  lemma : ∀ n t (x : ⊤) t' → OnPred (λ n1 → Sigma Nat (λ n0 → ⊤ → n1 == (n0 + binsum n))) t → t' == (t + binsum n) → OnPred (λ n'' → ∀ n0 → n'' == (n0 + binsum n) → t' == (n0 + Succ (binsum n + binsum n))) t
  lemma n t x t' (onPred (fst , snd)) refl with snd tt
  lemma n .(Succ (fst + binsum n)) x .(Succ ((fst + binsum n) + binsum n)) (onPred (fst , snd)) refl | refl = onPred λ n0 x₁ →
    trans (plus-succ (fst + binsum n) (binsum n)) (
    trans (plus-assoc fst (binsum n) (Succ (binsum n))) (
    trans (cong (\n' -> n' + (binsum n + Succ (binsum n))) ({!!} {fst} {n0} x₁)) (cong (λ n' → n0 + n') (sym (plus-succ (binsum n) (binsum n))))))
  -}
