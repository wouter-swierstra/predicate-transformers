{-# OPTIONS --type-in-type #-}
module Counter where

open import Prelude hiding (_⟨_⟩_)
open import Preorder
open import SliceSpec

data C : Set where
  Tick : C
R : C -> Set
R Tick = ⊤
Count = Slice Nat C R

tick : Count ⊤
tick = Step Tick return

ptCount : PTs Nat C R
ptCount Tick P n = P tt (Succ n)

-- We want to express this as a theorem on ptSlice,
-- since a theorem on Refine doesn't allow us to go specify
-- the value given after binding when we want to go into recursion.
ptAndBind : {b c : Set} -> {pre : Nat -> Set} {int : b -> Nat -> Set} {post : c -> Nat -> Set} ->
  (mx : Count b) -> (f : b -> Count c) ->
  ((n : Nat) -> pre n -> ptSlice ptCount int mx n) ->
  ((y : b) (n' : Nat) -> int y n' -> ptSlice ptCount post (f y) n') ->
  (n : Nat) -> pre n -> ptSlice ptCount post (mx >>= f) n
ptAndBind (Pure x₃) f x x₁ n x₂ = x₁ x₃ n (x n x₂)
ptAndBind (Step Tick k) f x x₁ n x₂ = ptAndBind (k tt) f (λ n₁ z → z) x₁ (Succ n) (x n x₂)
ptAndBind (Spec pre post k) f x x₁ n x₂ = Pair.fst (x n x₂) , (λ x₃ x₄ x₅ → ptAndBind (k x₄) f (λ n₁ z → z) x₁ x₃ (Pair.snd (x n x₂) x₃ x₄ x₅))

refineBind : {b c : Set} -> {pre : Nat -> Set} {int : Nat -> b -> Nat -> Set} ->
  (mx : Count b) -> (f : b -> Count c) ->
  Refine ptCount (spec pre int) mx ->
  Refine ptCount (spec pre int >>= f) (mx >>= f)
refineBind mx f x = refinement (λ P x₁ z → ptAndBind mx f (λ n z₁ → z₁) (λ y n' z₁ → z₁) x₁ (Refine.proof x (λ _ z₁ → ptSlice ptCount (P x₁) (f z₁)) x₁ (Pair.fst z , Pair.snd z)))

doBind : {b c : Set} -> {pre : Nat -> Set} {int : Nat -> b -> Nat -> Set} ->
  {post : Nat -> c -> Nat -> Set} ->
  Impl ptCount (spec pre int) ->
  ((y : b) -> Impl ptCount (spec (\n1 -> Sigma Nat (\n0 -> pre n0 -> int n0 y n1)) (\n1 z n2 -> (n0 : Nat) -> int n0 y n1 -> post n0 z n2))) ->
  Impl ptCount (spec pre post)
doBind {pre = pre} {int = int} {post = post} mx@(impl xprog xcode (refinement xproof)) f = impl
  (xprog >>= λ z → Impl.prog (f z))
  (isCodeBind xprog (\z -> Impl.prog (f z)) xcode (λ y → Impl.code (f y)))
  ((spec pre post
    ⟨ (refinement λ P x x₁ → Pair.fst x₁ , λ x' z x₂ → Refine.proof (Impl.refines (f z)) (λ _ → P x) x' ((x , (λ x₃ → x₂)) , (λ x₃ x₄ x₅ → Pair.snd x₁ x₃ x₄ (x₅ x x₂)))) ⟩
  spec pre int >>= (\z -> Impl.prog (f z))
    ⟨ refineBind xprog (λ z → Impl.prog (f z)) (refinement (λ P x z → xproof P x z)) ⟩
  (xprog >>= \z -> Impl.prog (f z)) ∎) pre-Refine)

data OnPred (P : Nat -> Set) : Nat -> Set where
  onPred : {n : Nat} -> P n -> OnPred P (Succ n)
fromPred : {n : Nat} {P : Nat -> Set} -> OnPred P (Succ n) -> P n
fromPred (onPred x) = x

doTick : {pre : Nat -> Set} {post : Nat -> ⊤ -> Nat -> Set} ->
  Impl ptCount (spec (OnPred pre) (\n y n' -> OnPred (\n'' -> post n'' y n') n)) ->
  Impl ptCount (spec pre post)
doTick (impl prog code (refinement proof)) = impl
  (tick >>= (λ _ → prog))
  (λ r → code)
  (refinement λ P x x₁ → proof (λ _ → P x) (Succ x) ((onPred (Pair.fst x₁)) , λ x' z x₂ → Pair.snd x₁ x' z (fromPred x₂)))

rep : Nat -> Slice Nat C R ⊤ -> Slice Nat C R ⊤
rep Zero m = return tt
rep (Succ n) m = m >>= \_ -> rep n m

hanoi : Nat -> Count ⊤
hanoi Zero = return tt
hanoi (Succ n) = hanoi n >>= \_ -> tick >>= \_ -> hanoi n

-- Sum of the first $n$ powers of $2$: $2^n - 1$.
binsum : Nat -> Nat
binsum Zero = 0
binsum (Succ n) = 1 + (binsum n + binsum n)

hanoiSpec : Nat -> Count ⊤
hanoiSpec n = spec (K ⊤) (λ i _ o → o == i + binsum n)

hanoiImpl : (n : Nat) -> Impl ptCount (hanoiSpec n)
hanoiImpl Zero = doReturn tt λ i o → plus-zero i
hanoiImpl (Succ n) = doBind (hanoiImpl n) λ _ →
  doTick (
  doSharpen (λ t _ → tt) (lemma n) (
  doBind (hanoiImpl n) \_ ->
  doReturn tt λ t x n0 x₁ → x₁ ))
  where -- prove stuff about binsum. This is a giant mess, but works :D
  lemma : ∀ n t (x : ⊤) t' → OnPred (λ n1 → Sigma Nat (λ n0 → ⊤ → n1 == (n0 + binsum n))) t → t' == (t + binsum n) → OnPred (λ n'' → ∀ n0 → n'' == (n0 + binsum n) → t' == (n0 + Succ (binsum n + binsum n))) t
  lemma n t x t' (onPred (fst , snd)) Refl with snd tt
  lemma n .(Succ (fst + binsum n)) x .(Succ ((fst + binsum n) + binsum n)) (onPred (fst , snd)) Refl | Refl = onPred λ n0 x₁ → trans (plus-succ (fst + binsum n) (binsum n)) (trans (plus-assoc fst (binsum n) (Succ (binsum n))) (trans (cong (\n' -> n' + (binsum n + Succ (binsum n))) (plus-inj {fst} {n0} x₁)) (cong (λ n' → n0 + n') (sym (plus-succ (binsum n) (binsum n))))))
