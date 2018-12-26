{-# OPTIONS --type-in-type #-}

open import Prelude hiding (_⟨_⟩_)
open import Maybe

open import Preorder
open Preorder.Preorder
open import WP
open import SliceSpec

module State where

data C (s : Set) : Set where
  Get : C s
  Put : s -> C s

R : (s : Set) -> C s -> Set
R s Get = s
R s (Put _)  = ⊤

fmapS : {a s : Set} {b : a -> Set} -> (f : (x : a) -> b x)
  -> (x : Pair a s) -> Pair (b (Pair.fst x)) s
fmapS f (fst , snd) = f fst , snd
prfmapS : {a s : Set} -> {b : a -> Set}
  -> (f : (x : a) -> b x) -> (x : Pair a s)
  -> f (Pair.fst x) == Pair.fst (fmapS f x)
prfmapS f (fst , snd) = refl

State : (s : Set) (b : Set) -> Set
State s b = Slice s (C s) (R s) b

instance
  Monad-State : {s : Set} -> IsMonad (\a -> s -> Pair a s)
  IsMonad.bind Monad-State mx f t = uncurry f (mx t)
  IsMonad.pure Monad-State x t = x , t
  IsMonad.left-identity Monad-State = refl
  IsMonad.right-identity Monad-State = refl

-- Smart constructors for State.
get : {s : Set} -> State s s
get = Step Get Pure
put : {s : Set} -> s -> State s ⊤
put x = Step (Put x) (λ _ → Pure tt)
modify : {s : Set} -> (s -> s) -> State s s
modify f = Step Get (\t -> Step (Put (f t)) \_ -> Pure t)
specState : {s : Set} {a : Set} {b : Set} ->
  (a -> s -> Set) -> (a -> s -> b -> s -> Set) -> a -> State s b
specState pre post x = spec (pre x) (post x)

_>=>_ : {a s : Set} -> {b c : Set}
  -> (a -> State s b) -> (b -> State s c) -> (a -> State s c)
f >=> g = \x -> f x >>= g

holds : {s : Set} -> PTs s (C s) (R s)
holds Get P t = P t t
holds (Put x) P t = P tt x

-- Does the stateful computation satisfy the predicate on the given initial state?
ptState : {a s : Set} -> (Q : a -> s -> Set) -> State s a -> s -> Set
ptState = ptSlice holds
-- Give the weakest precondition on input to f and initial state,
-- such that the (extended) postcondition holds.
wpState : {a s : Set} -> {b : Set}
  -> (P : a -> s -> b -> s -> Set)
  -> (f : a -> State s b)
  -> (a -> s -> Set)
wpState P f x t = ptState (P x t) (f x) t

-- Relation between holds and _>>=_
holdsBind : {a s : Set} -> {b : Set}
  -> (P : b -> s -> Set)
  -> (mx : State s a) -> (f : a -> State s b)
  -> (t : s) -> ptState (\x t' -> wpState (\_ _ -> P) f x t') mx t -> ptState P (mx >>= f) t
holdsBind P (Pure x) f t holdsX = holdsX
holdsBind P (Step Get k) f t holdsX = holdsBind P (k t) f t holdsX
holdsBind P (Step (Put t') k) f t holdsX = holdsBind P (k tt) f t' holdsX
holdsBind P (Spec pre post k) f t (fst , snd) = fst , λ x' z x → holdsBind P (k z) f x' (snd x' z x)

-- Relation between wpState and _>=>_
wpKleisli : {a s : Set} -> {b c : Set}
  -> (P : a -> s -> c -> s -> Set)
  -> (f : a -> State s b) -> (g : b -> State s c)
  -> (x : a) -> (t : s) ->
  wpState (λ _ _ → wpState (\_ _ -> P x t) g) f x t ->
  wpState P (f >=> g) x t
wpKleisli P f g x t wpF = holdsBind (P x t) (f x) g t wpF

-- If we have a Spec, then for any P, its precondition is implied by the wp.
holdsSpecPre : {a s : Set} -> {b : Set}
  -> (pre : a -> s -> Set)
  -> (post P : a -> s -> b -> s -> Set)
  -> (x : a) -> (t : s) ->
  wpState P (specState pre post) x t -> pre x t
holdsSpecPre pre post P x t = Pair.fst
-- If we have Spec pre post, then for any postcondition P that is implied by post, the wp is equivalent to pre.
holdsSpecPost : {a s : Set} -> {b : Set}
  -> (pre : a -> s -> Set)
  -> (post P : a -> s -> b -> s -> Set)
  -> ((x : a) -> (t : s) -> (y : b) -> (t' : s) -> post x t y t' -> P x t y t')
  -> (x : a) -> (t : s) ->
  pre x t -> wpState P (specState pre post) x t
holdsSpecPost pre post P postImplies x t preHolds
  = preHolds , (λ x₁ x₂ → postImplies x t x₂ x₁)

-- Define the refinement relation on wpState and show it's a preorder.
record _⊑_ {s : Set} {a : Set} {b : Set} (f g : a -> State s b) : Set1 where
  constructor refinement
  field
    proof : ∀ P x t -> wpState P f x t -> wpState P g x t
-- Define the refinement relation on holds and show it's a preorder.
record _⊑'_ {s : Set} {b : Set} (mx my : State s b) : Set1 where
  constructor refinement'
  field
    proof : ∀ P t -> ptState P mx t -> ptState P my t

⊑-refl : {a s : Set} {b : Set} (f : a -> State s b) -> f ⊑ f
⊑-refl f = refinement \ P x z x₁ → x₁
⊑-trans : {a s : Set} {b : Set} (f g h : a -> State s b) -> f ⊑ g -> g ⊑ h -> f ⊑ h
⊑-trans f g h (refinement proof) (refinement proof₁)
  = refinement (λ P x t z → proof₁ (λ _ _ → P x t) x t (proof (λ _ _ → P x t) x t z))

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
addRefinementArgument f g noArgs = refinement λ P x t pt → _⊑'_.proof (noArgs x) (P x t) t pt

-- Define how to execute stateful computations.
-- The handler only talks about how to update state when we encounter a command.
handleState : {s : Set} -> s -> (c : C s) -> Id (Pair (R s c) s)
handleState init Get = In (init , init)
handleState init (Put x) = In (tt , x)
runState : {a s : Set} -> (prog : State s a) -> isCodeSlice prog
  -> s -> Pair a s
runState prog prf t = out (runSlice IsMonad-Id handleState prog prf t)

-- wpState is sound: it gives a valid precondition
soundness : {a s : Set} -> {b : Set}
  -> (prog : a -> State s b) -> (prf : (x : a) -> isCodeSlice (prog x))
  -> (P : a -> s -> b -> s -> Set)
  -> (x : a) -> (t : s)
  -> wpState P prog x t
  -> uncurry (P x t) (runState (prog x) (prf x) t)
soundness {a} {s} {b} prog prf P x t wpHolds
  = soundness' (prog x) (prf x) (P x t) t wpHolds
  where
  soundness' : (prog : State s b) -> (prf : isCodeSlice prog)
    -> (P : b -> s -> Set)
    -> (t : s) -> ptState P prog t -> uncurry P (runState prog prf t)
  soundness' (Pure _) _ _ _ itHolds = itHolds
  soundness' (Step Get k) prf P t itHolds
    = soundness' (k t) (prf t) P t itHolds
  soundness' (Step (Put t') k) prf P _ itHolds
    = soundness' (k tt) (prf tt) P t' itHolds
  soundness' (Spec _ _ _) ()

-- wpState is complete: it gives a condition that is weaker than all preconditions
completeness' : {s : Set} -> {b : Set} -> (prog : State s b) -> (prf : isCodeSlice prog)
  -> (pre : s -> Set) -> (post : s -> b -> s -> Set)
  -> (t : s)
  -> pre t -> uncurry (post t) (runState prog prf t)
  -> ptState (post t) prog t
completeness' (Pure _) _ _ _ _ _ postHold = postHold
completeness' (Step Get k) prf pre post t preHold postHold
  = completeness' (k t) (prf t) pre post t preHold postHold
completeness' (Step (Put x) k) prf pre post t preHold postHold
  = completeness' (k tt) (prf tt) (\_ -> pre t) (\_ -> post t) x preHold postHold
completeness' (Spec _ _ _) ()

completeness : {a s : Set} -> {b : Set}
  -> (prog : a -> State s b) -> (prf : (x : a) -> isCodeSlice (prog x)) -- if we have code,
  -> (pre : a -> s -> Set) -> (post : a ->  s -> b -> s -> Set) -- and a specification
  -> ((x : a) -> (t : s) -> pre x t -> uncurry (post x t) (runState (prog x) (prf x) t)) -- and for all preconditioned values, the postcondition holds for running
  -> (x : a) -> (t : s) -> pre x t -> wpState post prog x t -- then it is stronger than the weakest precondition
completeness {a} {s} {b} prog prf pre post specRun x t preHolds
  = completeness' (prog x) (prf x) (pre x) (post x) t preHolds (specRun x t preHolds)

-- But the soundness and completeness only talk about code.
-- To relate it to specifications, we show the following lemma:
-- code refines all specifications that hold for running it.
-- Slogan: "a program is its own reference implementation."
refinePrePost : {a s : Set} -> {b : Set}
  -> (prog : a -> State s b) -> (prf : (x : a) -> isCodeSlice (prog x)) -- if we have code
  -> (pre : a -> s -> Set) -> (post : a -> s -> b -> s -> Set) -- and a specification
  -> ((x : a) -> (t : s) -> pre x t -> uncurry (post x t) (runState (prog x) (prf x) t)) -- and for all preconditioned values, the postcondition holds
  -> specState pre post ⊑ prog -- then the code refines the specification
refinePrePost {a} {s} {b} prog prf pre post postAfterRun = refinement prePost
  where
    rPP' : (prog : State s b) -> (prf : isCodeSlice prog)
      -> (pre : s -> Set) -> (post : s -> b -> s -> Set)
      -> ((t : s) -> pre t -> uncurry (post t) (runState prog prf t))
      -> (P : s -> b -> s -> Set)
      -> (x : a) -> (t : s) -> ptState (P t) (spec pre post) t
      -> ptState (P t) prog t
    rPP' prog prf pre post postAfterRun P x t (fst , snd)
      = let (y , t') = runState prog prf t
        in completeness' prog prf pre P t fst (snd t' y (postAfterRun t fst))
    prePost : (P : a -> s -> b -> s -> Set) -> (x : a) (t : s) -> wpState P (specState pre post) x t -> wpState P prog x t
    prePost P x t wpSpec = rPP' (prog x) (prf x) (pre x) (post x) (postAfterRun x) (P x) x t wpSpec

sharpenSpecState : {a s : Set} {b : Set} ->
  (pre pre' : a -> s -> Set) ->
  (post post' : a -> s -> b -> s -> Set) ->
  (∀ x t -> pre x t -> pre' x t) ->
  (∀ x t y t' -> pre x t -> post' x t y t' -> post x t y t') ->
  specState pre post ⊑ specState pre' post'
sharpenSpecState {a} {s} {b} pre pre' post post' sh we = refinement sharpen'
  where
  sharpen' : (P : a -> s -> b -> s -> Set) -> (x : a) (t : s) ->
    wpState P (specState pre post) x t -> wpState P (specState pre' post') x t
  sharpen' P x t pf
    = sh x t (Pair.fst pf) ,
        (λ x₁ x₂ x₃ → Pair.snd pf x₁ x₂ (we x t x₂ x₁ (Pair.fst pf) x₃))
sharpenSpec' : {s : Set} {b : Set} ->
  (pre pre' : s -> Set) ->
  (post post' : s -> b -> s -> Set) ->
  (∀ t -> pre t -> pre' t) ->
  (∀ t y t' -> pre t -> post' t y t' -> post t y t') ->
  spec pre post ⊑' spec pre' post'
sharpenSpec' {s} {b} pre pre' post post' sh we = refinement' λ P t x → sharpen' (\_ -> P) t x
  where
  sharpen' : (P : s -> b -> s -> Set) -> (t : s) ->
    ptState (P t) (spec pre post) t -> ptState (P t) (spec pre' post') t
  sharpen' P t pf = sh t (Pair.fst pf) , λ x t' z → Pair.snd pf x t' (we t t' x (Pair.fst pf) z)

-- How to refine a specification by doing a Get:
-- the state gets passed to the first and second argument,
-- so they should be equal.
preGet : {s : Set} ->
  (P : s -> Set) ->
  s -> s -> Set
preGet P t t' = Pair (t == t') (P t)
postGet : {s : Set} -> {b : Set} ->
  (Q : s -> b -> s -> Set) ->
  s -> s -> b -> s -> Set
postGet Q t t' x to = Pair (t == t') (Q t x to)

-- Turn a general precondition into a precondition for
-- the continuation of Put.
-- We need to ensure that the state for the pre- and postcondition are equal,
-- so we have to move the precondition to the postcondition.
prePut : {s : Set} -> {b : Set} ->
  (t : s) ->
  (P : s -> Set) -> (Q : s -> b -> s -> Set) ->
  ⊤ -> s -> Set
prePut {s} t P Q tt t' = (t == t')
postPut : {s : Set} {b : Set} ->
  (t : s) ->
  (P : s -> Set) -> (Q : s -> b -> s -> Set) ->
  ⊤ -> s -> b -> s -> Set
postPut {s} t P Q tt t' x to = (t : s) -> P t -> Q t x to

refineGet : {s : Set} -> {b : Set} ->
  (P : s -> Set) ->
  (Q : s -> b -> s -> Set) ->
  spec P Q ⊑' (get >>= specState (preGet P) (postGet Q))
refineGet {s} {b} P Q = refinement' λ P₁ t x → (refl , Pair.fst x) , (λ x₁ x₂ x₃ → Pair.snd x x₁ x₂ (Pair.snd x₃))
refineUnderGet : {s : Set} {b : Set} ->
  (prog prog' : s -> State s b) ->
  (prog ⊑ prog') ->
  (get >>= prog) ⊑' (get >>= prog')
refineUnderGet prog prog' prf = refinement' λ P' t wpProg →
  _⊑_.proof prf (λ _ _ → P') t t wpProg
refinePut : {s : Set} -> {b : Set}
  -> (P : s -> Set)
  -> (Q : s -> b -> s -> Set)
  -> (t : s)
  -> spec P Q ⊑' (put t >>= specState (prePut t P Q) (postPut t P Q))
refinePut {s} {b} P Q t = refinement' λ P₁ t₁ x → refl , (λ x₁ x₂ x₃ → Pair.snd x x₁ x₂ (x₃ t₁ (Pair.fst x)))

refineUnderPut : {s : Set} {b : Set} ->
  (t : s) ->
  (prog prog' : State s b) ->
  (prog ⊑' prog') ->
  (put t >>= \_ -> prog) ⊑' (put t >>= \_ -> prog')
refineUnderPut t prog prog' prf = refinement' \P' _ wpProg -> _⊑'_.proof prf P' t wpProg

-- The type of all implementations of a given specification.
record Impl' {s : Set} {b : Set} (spec : State s b) : Set where
  constructor impl
  field
    prog : State s b
    code : isCodeSlice prog
    refines : spec ⊑' prog
open Impl'

-- Combinators for 'easy' proofs of Impl.
doSharpenState : {a s : Set} ->
  {pre pre' : s -> Set} ->
  {post post' : s -> a -> s -> Set} ->
  ((t : s) -> pre t -> pre' t) ->
  ((t : s) -> (x : a) -> (t' : s) -> pre t -> post' t x t' -> post t x t') ->
  Impl' (spec pre' post') ->
  Impl' (spec pre post)
doSharpenState {a} {s} {pre} {pre'} {post} {post'} x x₁ (impl prog₁ code₁ refines₁) = impl prog₁ code₁
  ((spec pre post ⟨ sharpenSpec' pre pre' post post' x x₁ ⟩ spec pre' post' ⟨ refines₁ ⟩ (prog₁ ∎)) pre-⊑')

doReturnState : {a s : Set} ->
  (post : s -> a -> s -> Set) ->
  (x : a) ->
  Impl' (spec (\t -> post t x t) post)
doReturnState {a} {s} post x = impl
  (Pure x)
  tt
  (refinement' (λ P t z → Pair.snd z t x (Pair.fst z)))

doGet : {s : Set} -> {b : Set} ->
  {pre : s -> Set} ->
  {post : s -> b -> s -> Set} ->
  ((t : s) -> Impl' (spec (preGet pre t) (postGet post t))) ->
  Impl' (spec pre post)
doGet {s} {b} {pre} {post} cases = impl
  (get >>= \t -> prog (cases t))
  (λ t → code (cases t))
  ((spec pre post
      ⟨ refineGet pre post ⟩
    (get >>= specState (preGet pre) (postGet post))
      ⟨ refineUnderGet (specState (preGet pre) (postGet post)) (\t -> prog (cases t)) (addRefinementArgument (specState (preGet pre) (postGet post)) (\t -> prog (cases t)) \t -> refines (cases t)) ⟩
    (get >>= \t -> prog (cases t)) ∎) pre-⊑')
  where

doPut : {s : Set} -> {b : Set} ->
  {pre : s -> Set} ->
  {post : s -> b -> s -> Set} ->
  (t : s) ->
  Impl' (spec (prePut t pre post tt) (postPut t pre post tt)) ->
  Impl' (spec pre post)
doPut {s} {b} {pre} {post} t cases = impl
  (put t >>= \_ -> prog cases)
  (const (code cases))
  ((spec pre post
      ⟨ refinePut pre post t ⟩
    (put t >>= specState (prePut t pre post) (postPut t pre post))
      ⟨ refineUnderPut t (specState (prePut t pre post) (postPut t pre post) tt) (prog cases) (refines cases) ⟩
    (put t >>= \_ -> prog cases) ∎) pre-⊑')
  where

-- Specify the incrementation program: give the current state and update it by incrementing.
incrPost : Nat -> Nat -> Nat -> Set
incrPost n n' n+1 = Pair (n == n') (Succ n == n+1)
incrSpec : State Nat Nat
incrSpec = spec (\_ -> ⊤) incrPost

incrImpl : Impl' incrSpec
incrImpl =
  doGet \n ->
  doPut (Succ n) (
  doSharpenState (λ t x → x , refl , x) (λ t x t' x₁ x₂ t₁ x₃ → Pair.fst x₃ , (Triple.snd x₂ , Triple.thd x₂)) (
  doReturnState (\n+1 n' n+1' -> Triple (Succ n == n+1) (n == n') (Succ n == n+1')) n))
