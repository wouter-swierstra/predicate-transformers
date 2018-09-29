{-# OPTIONS --type-in-type #-}

open import Prelude hiding (_⟨_⟩_)
open import Maybe

open import Preorder
open Preorder.Preorder
open import Spec

module State where

module StateMonad (s : Set) where
  data C : Set where
    Get : C
    Put : s -> C

  R : C -> Set
  R Get = s
  R (Put _)  = ⊤

  fmapS : {a : Set} {b : a -> Set} -> (f : (x : a) -> b x)
    -> (x : Pair a s) -> Pair (b (Pair.fst x)) s
  fmapS f (fst , snd) = f fst , snd
  prfmapS : {a : Set} -> {b : a -> Set}
    -> (f : (x : a) -> b x) -> (x : Pair a s)
    -> f (Pair.fst x) == Pair.fst (fmapS f x)
  prfmapS f (fst , snd) = Refl

  State : (b : Set) -> Set
  State = Mix C R

open StateMonad

Monad-State : {s : Set} -> IsMonad (\a -> s -> Pair a s)
IsMonad.bind Monad-State mx f t = uncurry f (mx t)
IsMonad.pure Monad-State x t = x , t

-- Smart constructors for State.
get : {s : Set} -> State s s
get = Step Get return
put : {s : Set} -> s -> State s ⊤
put x = Step (Put x) (λ _ → return tt)
modify : {s : Set} -> (s -> s) -> State s s
modify f = Step Get (\t -> Step (Put (f t)) \_ -> return t)
-- In contrast to Spec.spec, which ignores effects,
-- in State we tend to use the state in pre- and postconditions.
-- We access it using the Get and Put operations.
-- spec' is an intermediate for specState.
spec' : {s : Set} {a : Set} -> (s -> Set) -> (s -> Pair a s -> Set) -> State s a
spec' pre post = Step Get (\t -> Spec (pre t) (post t) \f -> (Step (Put (² f)) \_ -> return (¹ f)))
specState : {s : Set} {a : Set} {b : Set} ->
  (Pair a s -> Set) -> (Pair a s -> Pair b s -> Set) -> a -> State s b
specState pre post x = spec' (\t -> pre (x , t)) (\t -> post (x , t))

_>>=_ : {a s : Set} -> {b : Set} -> State s a -> (a -> State s b) -> State s b
Pure x >>= f = f x
Step c k >>= f = Step c \x -> k x >>= f
Spec pre post k >>= f = Spec pre post \x -> k x >>= f
_>=>_ : {a s : Set} -> {b c : Set}
  -> (a -> State s b) -> (b -> State s c) -> (a -> State s c)
f >=> g = \x -> f x >>= g

holds : {a s : Set}
  -> (P : Pair a s -> Set)
  -> (t : s)
  -> (prog : State s a) -> Set
holds P t (Pure x) = P (x , t)
holds P t (Step Get k) = holds P t (k t)
holds P t (Step (Put x) k) = holds P x (k tt)
holds {s = s} P t (Spec {b} pre post k) = Pair pre -- if precondition holds
  ((x : b) -> (t' : s) -> post x -- and for all intermediate values such that the postcondition holds,
    -> holds P t' (k x)) -- then the continuation makes P hold

wpState : {a s : Set} -> {b : Set}
  -> (P : Pair a s -> Pair b s -> Set)
  -> (f : a -> State s b)
  -> (Pair a s -> Set)
wpState P f (x , t) = wp (\y -> holds (P (y , t)) t) f x

-- Relation between holds and _>>=_
holdsBind : {a s : Set} -> {b : Set}
  -> (P : Pair b s -> Set)
  -> (mx : State s a) -> (f : a -> State s b)
  -> (t : s) -> holds (wpState (\i o -> P o) f) t mx -> holds P t (mx >>= f)
holdsBind P (Pure x) f t holdsX = holdsX
holdsBind P (Step Get k) f t holdsX = holdsBind P (k t) f t holdsX
holdsBind P (Step (Put x) k) f t holdsX = holdsBind P (k tt) f x holdsX
holdsBind P (Spec pre post k) f t (fst , snd) = fst , (λ x t' x₁ → holdsBind P (k x) f t' (snd x t' x₁))

-- Relation between wpState and _>=>_
wpKleisli : {a s : Set} -> {b c : Set}
  -> (P : Pair a s -> Pair c s -> Set)
  -> (f : a -> State s b) -> (g : b -> State s c)
  -> wpState (λ i m → wpState (λ m o → P i o) g m) f ⊆ wpState P (f >=> g)
wpKleisli P f g (x , t) wpF = holdsBind (P (x , t)) (f x) g t wpF

-- If we have a Spec, then for any P, its precondition is implied by the wp.
holdsSpecPre : {a s : Set} -> {b : Set}
  -> (pre : Pair a s -> Set)
  -> (post P : Pair a s -> Pair b s -> Set)
  -> wpState P (specState pre post) ⊆ pre
holdsSpecPre pre post P (x , t) (fst , snd) = fst
-- If we have Spec pre post, then for any postcondition P that is implied by post, the wp is equivalent to pre.
holdsSpecPost : {a s : Set} -> {b : Set}
  -> (pre : Pair a s -> Set)
  -> (post P : Pair a s -> Pair b s -> Set)
  -> ((x : Pair a s) -> (y : Pair b s) -> post x y -> P x y)
  -> pre ⊆ wpState P (specState pre post)
holdsSpecPost pre post P postImplies (x , t) preHolds
  = preHolds , λ x₁ t' x₂ → postImplies (x , t) x₁ x₂

-- Define the refinement relation on wpState and show it's a preorder.
record _⊑_ {s : Set} {a : Set} {b : Set} (f g : a -> State s b) : Set1 where
  constructor refinement
  field
    proof : ∀ P -> wpState P f ⊆ wpState P g
-- Define the refinement relation on holds and show it's a preorder.
record _⊑'_ {s : Set} {b : Set} (mx my : State s b) : Set1 where
  constructor refinement'
  field
    proof : ∀ P t -> holds P t mx -> holds P t my

⊑-refl : {a s : Set} {b : Set} (f : a -> State s b) -> f ⊑ f
⊑-refl f = refinement \ P x z -> z
⊑-trans : {a s : Set} {b : Set} (f g h : a -> State s b) -> f ⊑ g -> g ⊑ h -> f ⊑ h
⊑-trans f g h x x₁ = refinement \P x₂ x₃ -> _⊑_.proof x₁ P x₂ (_⊑_.proof x P x₂ x₃)

pre-⊑ : ∀ {a b c} -> Preorder (_⊑_ {a} {b} {c})
pre-⊑ = preorder (\{f} -> ⊑-refl f) (\{f} {g} {h} -> ⊑-trans f g h)
pre-⊑' : ∀ {b c} -> Preorder (_⊑'_ {b} {c})
pre-⊑' = preorder
  (λ {x} → refinement' (λ P t z → z))
  (λ {x} {y} {z} z₁ z₂ → refinement' (λ P t z₃ → _⊑'_.proof z₂ P t (_⊑'_.proof z₁ P t z₃)))

-- How to get ⊑ from ⊑'
addRefinementArgument : {a s : Set} -> {b : Set}
  -> (f g : a -> State s b)
  -> ((x : a) -> f x ⊑' g x)
  -> f ⊑ g
addRefinementArgument f g noArgs = refinement λ P x₁ x₂ → _⊑'_.proof (noArgs (Pair.fst x₁)) (P x₁) (Pair.snd x₁) x₂

-- Define how to execute stateful computations.
-- The handler only talks about how to update state when we encounter a command.
handleState : {s : Set} -> (c : C s) -> s -> (Pair (R s c) s)
handleState Get init = init , init
handleState (Put x) init = tt , x
runState : {a s : Set} -> (prog : State s a) -> isCode prog
  -> s -> Pair a s
runState = run Monad-State handleState

-- wpState is sound: it gives a valid precondition
soundness : {a s : Set} -> {b : Set}
  -> (prog : a -> State s b) -> (prf : (x : a) -> isCode (prog x))
  -> (P : Pair a s -> Pair b s -> Set)
  -> (x : a) -> (t : s)
  -> wpState P prog (x , t)
  -> P (x , t) (runState (prog x) (prf x) t)
soundness {a} {s} {b} prog prf P x t wpHolds
  = soundness' (prog x) (prf x) (P (x , t)) t wpHolds
  where
  soundness' : (prog : State s b) -> (prf : isCode prog)
    -> (P : Pair b s -> Set)
    -> (t : s) -> holds P t prog -> P (runState prog prf t)
  soundness' (Pure _) _ _ _ itHolds = itHolds
  soundness' (Step Get k) prf P t itHolds
    = soundness' (k t) (prf t) P t itHolds
  soundness' (Step (Put t') k) prf P _ itHolds
    = soundness' (k tt) (prf tt) P t' itHolds
  soundness' (Spec _ _ _) ()

-- wpState is complete: it gives a condition that is weaker than all preconditions
completeness' : {s : Set} -> {b : Set} -> (prog : State s b) -> (prf : isCode prog)
  -> (pre : s -> Set) -> (post : Pair b s -> Set)
  -> (t : s)
  -> pre t -> post (runState prog prf t)
  -> holds post t prog
completeness' (Pure _) _ _ _ _ _ postHold = postHold
completeness' (Step Get k) prf pre post t preHold postHold
  = completeness' (k t) (prf t) (λ _ → pre t) post t preHold postHold
completeness' (Step (Put x) k) prf pre post t preHold postHold
  = completeness' (k tt) (prf tt) (λ _ → pre t) post x preHold postHold
completeness' (Spec _ _ _) ()

completeness : {a s : Set} -> {b : Set}
  -> (prog : a -> State s b) -> (prf : (x : a) -> isCode (prog x)) -- if we have code,
  -> (pre : Pair a s -> Set) -> (post : Pair a s -> Pair b s -> Set) -- and a specification
  -> ((x : a) -> (t : s) -> pre (x , t) -> post (x , t) (runState (prog x) (prf x) t)) -- and for all preconditioned values, the postcondition holds for running
  -> (x : a) -> (t : s) -> pre (x , t) -> wpState post prog (x , t) -- then it is stronger than the weakest precondition
completeness {a} {s} {b} prog prf pre post specRun x t preHolds
  = completeness' (prog x) (prf x) (\t -> pre (x , t)) (post (x , t)) t preHolds (specRun x t preHolds)

-- But the soundness and completeness only talk about code.
-- To relate it to specifications, we show the following lemma:
-- code refines all specifications that hold for running it.
-- Slogan: "a program is its own reference implementation."
refinePrePost : {a s : Set} -> {b : Set}
  -> (prog : a -> State s b) -> (prf : (x : a) -> isCode (prog x)) -- if we have code
  -> (pre : Pair a s -> Set) -> (post : Pair a s -> Pair b s -> Set) -- and a specification
  -> ((x : a) -> (t : s) -> pre (x , t) -> post (x , t) (runState (prog x) (prf x) t)) -- and for all preconditioned values, the postcondition holds
  -> specState pre post ⊑ prog -- then the code refines the specification
refinePrePost {a} {s} {b} prog prf pre post postAfterRun = refinement prePost
  where
    rPP' : (prog : State s b) -> (prf : isCode prog)
      -> (pre : s -> Set) -> (post : s -> Pair b s -> Set)
      -> ((t : s) -> pre t -> post t (runState prog prf t))
      -> (P : Pair b s -> Set)
      -> (x : a) -> (t : s) -> holds P t (spec' pre post)
      -> holds P t prog
    rPP' prog prf pre post postAfterRun P x t (preHolds , postImpliesP)
      = let (y , t') = runState prog prf t
        in completeness' prog prf pre P t preHolds
            (postImpliesP (y , t') t' (postAfterRun t preHolds))
    prePost : (P : Pair a s -> Pair b s -> Set) -> (x : Pair a s) -> wpState P (specState pre post) x -> wpState P prog x
    prePost P (x , t) wpSpec = rPP' (prog x) (prf x) (λ z → pre (x , z)) (\z -> post (x , z)) (postAfterRun x) (P (x , t)) x t wpSpec

sharpenSpec : {a s : Set} {b : Set} ->
  (pre pre' : Pair a s -> Set) ->
  (post post' : Pair a s -> Pair b s -> Set) ->
  (∀ i -> pre i -> pre' i) ->
  (∀ i o -> pre i -> post' i o -> post i o) ->
  specState pre post ⊑ specState pre' post'
sharpenSpec {a} {s} {b} pre pre' post post' sh we = refinement sharpen'
  where
  sharpen' : (P : Pair a s -> Pair b s -> Set) -> (i : Pair a s) ->
    wpState P (specState pre post) i -> wpState P (specState pre' post') i
  sharpen' P i (fst , snd)
    = sh i fst
    , λ x t' x₁ → snd x t' (we i x fst x₁)
sharpenSpec' : {s : Set} {b : Set} ->
  (pre pre' : s -> Set) ->
  (post post' : s -> Pair b s -> Set) ->
  (∀ i -> pre i -> pre' i) ->
  (∀ i o -> pre i -> post' i o -> post i o) ->
  spec' pre post ⊑' spec' pre' post'
sharpenSpec' {s} {b} pre pre' post post' sh we = refinement' sharpen'
  where
  sharpen' : (P : Pair b s -> Set) -> (t : s) ->
    holds P t (spec' pre post) -> holds P t (spec' pre' post')
  sharpen' P t (fst , snd) = (sh t fst) , (λ x t' z → snd x t' (we t x fst z))

-- How to refine a specification by doing a Get:
-- the state gets passed to the first and second argument,
-- so they should be equal.
preGet : {s : Set} ->
  (P : s -> Set) ->
  Pair s s -> Set
preGet P (t , t') = Pair (t == t') (P t)
postGet : {s : Set} -> {b : Set} ->
  (Q : s -> Pair b s -> Set) ->
  Pair s s -> Pair b s -> Set
postGet Q (t , t') o = Pair (t == t') (Q t o)

-- Turn a general precondition into a precondition for
-- the continuation of Put.
-- We need to ensure that the state for the pre- and postcondition are equal,
-- so we have to move the precondition to the postcondition.
prePut : {s : Set} -> {b : Set} ->
  (t : s) ->
  (P : s -> Set) -> (Q : s -> Pair b s -> Set) ->
  Pair ⊤ s -> Set
prePut {s} t P Q (tt , t') = (t == t')
postPut : {s : Set} {b : Set} ->
  (t : s) ->
  (P : s -> Set) -> (Q : s -> Pair b s -> Set) ->
  Pair ⊤ s -> Pair b s -> Set
postPut {s} t P Q (tt , t') o = (t : s) -> P t -> Q t o

refineGet : {s : Set} -> {b : Set} ->
  (P : s -> Set) ->
  (Q : s -> Pair b s -> Set) ->
  spec' P Q ⊑' (get >>= specState (preGet P) (postGet Q))
refineGet {s} {b} P Q = refinement' λ P₁ t x → (Refl , Pair.fst x) , (λ x₁ x₂ x₃ → Pair.snd x x₁ x₂ (Pair.snd x₃))
refineUnderGet : {s : Set} {b : Set} ->
  (prog prog' : s -> State s b) ->
  (prog ⊑ prog') ->
  (get >>= prog) ⊑' (get >>= prog')
refineUnderGet prog prog' prf = refinement' λ P' t wpProg →
  holdsBind P' get prog' t (_⊑_.proof prf (λ x → P') (t , t) wpProg)
refinePut : {s : Set} -> {b : Set}
  -> (P : s -> Set)
  -> (Q : s -> Pair b s -> Set)
  -> (t : s)
  -> spec' P Q ⊑' (put t >>= specState (prePut t P Q) (postPut t P Q))
refinePut {s} {b} P Q t = refinement' λ P₁ t₁ x → Refl , λ x₁ t' x₂ → (² x) x₁ t' (x₂ t₁ (¹ x))

refineUnderPut : {s : Set} {b : Set} ->
  (t : s) ->
  (prog prog' : State s b) ->
  (prog ⊑' prog') ->
  (put t >>= \_ -> prog) ⊑' (put t >>= \_ -> prog')
refineUnderPut t prog prog' prf = refinement' \P' _ wpProg ->
  _⊑'_.proof prf P' t wpProg

-- The type of all implementations of a given specification.
record Impl' {s : Set} {b : Set} (spec : State s b) : Set where
  constructor impl
  field
    prog : State s b
    code : isCode prog
    refines : spec ⊑' prog
open Impl'

-- Combinators for 'easy' proofs of Impl.
doSharpen : {a s : Set} ->
  {pre pre' : s -> Set} ->
  {post post' : s -> Pair a s -> Set} ->
  ((t : s) -> pre t -> pre' t) ->
  ((t : s) -> (o : Pair a s) -> pre t -> post' t o -> post t o) ->
  Impl' (spec' pre' post') ->
  Impl' (spec' pre post)
doSharpen {a} {s} {pre} {pre'} {post} {post'} x x₁ (impl prog₁ code₁ refines₁) = impl prog₁ code₁
  ((spec' pre post ⟨ sharpenSpec' pre pre' post post' x x₁ ⟩ spec' pre' post' ⟨ refines₁ ⟩ (prog₁ ∎)) pre-⊑')

doReturn : {a s : Set} ->
  (post : s -> Pair a s -> Set) ->
  (x : a) ->
  Impl' (spec' (\t -> post t (x , t)) post)
doReturn {a} {s} post x = impl
  (return x)
  tt
  (refinement' (λ P t z → Pair.snd z (x , t) t (Pair.fst z)))

doGet : {s : Set} -> {b : Set} ->
  {pre : s -> Set} ->
  {post : s -> Pair b s -> Set} ->
  ((t : s) -> Impl' (spec' (\t' -> preGet pre (t , t')) (\t' -> postGet post (t , t')))) ->
  Impl' (spec' pre post)
doGet {s} {b} {pre} {post} cases = impl
  (get >>= \t -> prog (cases t))
  (λ t → code (cases t))
  ((spec' pre post
      ⟨ refineGet pre post ⟩
    (get >>= specState (preGet pre) (postGet post))
      ⟨ refineUnderGet (specState (preGet pre) (postGet post)) (\t -> prog (cases t)) (addRefinementArgument (specState (preGet pre) (postGet post)) (\t -> prog (cases t)) \t -> refines (cases t)) ⟩
    (get >>= \t -> prog (cases t)) ∎) pre-⊑')
  where

doPut : {s : Set} -> {b : Set} ->
  {pre : s -> Set} ->
  {post : s -> Pair b s -> Set} ->
  (t : s) ->
  Impl' (spec' (\t' -> prePut t pre post (tt , t')) (\t' -> postPut t pre post (tt , t'))) ->
  Impl' (spec' pre post)
doPut {s} {b} {pre} {post} t cases = impl
  (put t >>= \_ -> prog cases)
  (const (code cases))
  ((spec' pre post
      ⟨ refinePut pre post t ⟩
    (put t >>= specState (prePut t pre post) (postPut t pre post))
      ⟨ refineUnderPut t (specState (prePut t pre post) (postPut t pre post) tt) (prog cases) (refines cases) ⟩
    (put t >>= \_ -> prog cases) ∎) pre-⊑')
  where

-- Specify the incrementation program: give the current state and update it by incrementing.
incrPost : Nat -> Pair Nat Nat -> Set
incrPost n (n' , n+1) = Pair (n == n') (Succ n == n+1)
incrSpec : State Nat Nat
incrSpec = spec' (\_ -> ⊤) incrPost

incrImpl : Impl' incrSpec
incrImpl =
  doGet \n ->
  doPut (Succ n) (
  doSharpen (λ t x → x , Refl , x) (λ t o x x₁ t₁ x₂ → (Pair.fst x₂) , ((Triple.snd x₁) , (Triple.thd x₁))) (
  doReturn (\n+1 n,n+1 -> Triple (Succ n == n+1) (n == Pair.fst n,n+1) (Succ n == Pair.snd n,n+1)) n))
