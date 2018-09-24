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
  rtState : RunType
  rtState = types
    (\b -> Pair b s) Pair.fst fmapS prfmapS
    (\b -> Pair b s) Just (λ f x → f (Pair.fst x) , Pair.snd x) (λ f x → Refl)
    (\x f -> f x)

  State : (b : Set) -> Set
  State = Mix C R rtState

open StateMonad
open RunType

-- Smart constructors for State.
get : {s : Set} -> State s s
get = Step Get return
put : {s : Set} -> s -> State s ⊤
put x = Step (Put x) (λ _ → return tt)
modify : {s : Set} -> (s -> s) -> State s s
modify f = Step Get (\t -> Step (Put (f t)) \_ -> return t)

_>>=_ : {a s : Set} -> {b : Set} -> State s a -> (a -> State s b) -> State s b
Pure x >>= f = f x
Step c k >>= f = Step c \x -> k x >>= f
Spec pre post k >>= f = Spec pre post \x -> k x >>= f
_>=>_ : {a s : Set} -> {b c : Set}
  -> (a -> State s b) -> (b -> State s c) -> (a -> State s c)
f >=> g = \x -> f x >>= g

-- TODO: define it like this? We have to prove termination though...
{-
holds : {a s : Set}
  -> (P : Pair a s -> Set)
  -> (x : Pair ⊤ s)
  -> (c : C s) -> (k : R s c -> State s a) -> Set
holds P init Get k = ptMix holds P init (k (Pair.snd init))
holds P init (Put next) k = {!!}
-}

holds : {a s : Set}
  -> (P : Pair a s -> Set)
  -> (t : s)
  -> (prog : State s a) -> Set
holds P t (Pure x) = P (x , t)
holds P t (Step Get k) = holds P t (k t)
holds P t (Step (Put x) k) = holds P x (k tt)
holds {s = s} P t (Spec {b} pre post k) = Pair (pre ⊤ (tt , t)) -- if precondition holds
  ((x : b) -> (t' : s) -> post ⊤ (tt , t) (x , t') -- and for all intermediate values such that the postcondition holds,
    -> holds P t' (k x)) -- then the continuation makes P hold

wpState : {a s : Set} -> {b : a -> Set}
  -> (P : Post (rtState s) a b)
  -> (f : (x : a) -> State s (b x))
  -> (Pre (rtState s) a)
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
  -> (P : Post (rtState s) a (K c))
  -> (f : a -> State s b) -> (g : b -> State s c)
  -> wpState (λ i m → wpState (λ m o → P i o) g m) f ⊆ wpState P (f >=> g)
wpKleisli P f g (x , t) wpF = holdsBind (P (x , t)) (f x) g t wpF

-- If we have a Spec, then for any P, its precondition is implied by the wp.
holdsSpecPre : {a s : Set} -> {b : a -> Set}
  -> (pre : Pre (rtState s) a)
  -> (post P : Post (rtState s) a b)
  -> wpState P (spec pre post) ⊆ pre
holdsSpecPre pre post P (x , t) (fst , snd) = fst
-- If we have Spec pre post, then for any postcondition P that is implied by post, the wp is equivalent to pre.
holdsSpecPost : {a s : Set} -> {b : a -> Set}
  -> (pre : Pre (rtState s) a)
  -> (post P : Post (rtState s) a b)
  -> ((x : Pair a s) -> (y : tyO (rtState s) (b (Pair.fst x))) -> post x y -> P x y)
  -> pre ⊆ wpState P (spec pre post)
holdsSpecPost pre post P postImplies (x , t) preHolds
  = preHolds , (λ y t' postHolds → postImplies (x , t) (y , t') postHolds)

-- Define the refinement relation on wpState and show it's a preorder.
record _⊑_ {s : Set} {a : Set} {b : Set} (f g : a -> State s b) : Set1 where
  constructor refinement
  field
    proof : ∀ P -> wpState P f ⊆ wpState P g

⊑-refl : {a s : Set} {b : Set} (f : a -> State s b) -> f ⊑ f
⊑-refl f = refinement \ P x z -> z
⊑-trans : {a s : Set} {b : Set} (f g h : a -> State s b) -> f ⊑ g -> g ⊑ h -> f ⊑ h
⊑-trans f g h x x₁ = refinement \P x₂ x₃ -> _⊑_.proof x₁ P x₂ (_⊑_.proof x P x₂ x₃)

pre-⊑ : ∀ {a b c} -> Preorder (_⊑_ {a} {b} {c})
pre-⊑ = preorder (\{f} -> ⊑-refl f) (\{f} {g} {h} -> ⊑-trans f g h)

-- Define how to execute stateful computations.
-- The handler only talks about how to update state when we encounter a command.
handleState : {s : Set} -> (init : Pair ⊤ s) -> (c : C s) -> (Pair (R s c) s)
handleState (_ , init) Get = init , init
handleState (_ , init) (Put x) = tt , x
runState : {a s : Set} -> (prog : State s a) -> isCode prog
  -> s -> Pair a s
runState prog prf init = run handleState prog prf (tt , init)

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
  -> spec pre post ⊑ prog -- then the code refines the specification
refinePrePost {a} {s} {b} prog prf pre post postAfterRun = refinement prePost
  where
    rPP' : (prog : State s b) -> (prf : isCode prog)
      -> (pre : s -> Set) -> (post : s -> Pair b s -> Set)
      -> ((t : s) -> pre t -> post t (runState prog prf t))
      -> (P : Pair b s -> Set)
      -> (x : a) -> (t : s) -> holds P t (spec (\i -> pre (Pair.fst i)) (\i -> post (Pair.fst i)) t)
      -> holds P t prog
    rPP' prog prf pre post postAfterRun P x t (preHolds , postImpliesP)
      = let (y , t') = runState prog prf t
        in completeness' prog prf pre P t preHolds
            (postImpliesP y t' (postAfterRun t preHolds))
    prePost : (P : Pair a s -> Pair b s -> Set) -> (x : Pair a s) -> wpState P (spec pre post) x -> wpState P prog x
    prePost P (x , t) wpSpec = rPP' (prog x) (prf x) (λ z → pre (x , z)) (\z -> post (x , z)) (postAfterRun x) (P (x , t)) x t wpSpec

sharpenSpec : {a s : Set} {b : Set} ->
  (pre pre' : Pair a s -> Set) ->
  (post post' : Pair a s -> Pair b s -> Set) ->
  (∀ i -> pre i -> pre' i) ->
  (∀ i o -> pre i -> post' i o -> post i o) ->
  spec pre post ⊑ spec pre' post'
sharpenSpec {a} {s} {b} pre pre' post post' sh we = refinement sharpen'
  where
  sharpen' : (P : Pair a s -> Pair b s -> Set) -> (i : Pair a s) ->
    wpState P (spec pre post) i -> wpState P (spec pre' post') i
  sharpen' P i (fst , snd)
    = sh i fst
    , λ x t' x₁ → snd x t' (we i (x , t') fst x₁)

-- How to refine a specification by doing a Get:
-- instead of caring about the first argument to the pre- and postcondition,
-- we want to know about the state.
preGet : {a s : Set}
  -> (P : Pair s s -> Set)
  -> Pair a s -> Set
preGet P i = P (Pair.snd i , Pair.snd i)
postGet : {a s : Set} -> {b : Set}
  -> (Q : Pair s s -> Pair b s -> Set)
  -> Pair a s -> Pair b s -> Set
postGet Q i = Q (Pair.snd i , Pair.snd i)
-- The same for Put:
-- instead of caring about whatever we put,
-- we want to know about the input to the value that was put.
prePut : {a s : Set}
  -> (f : a -> s)
  -> (P : Pair ⊤ s -> Set)
  -> Pair a s -> Set
prePut f P (x , t) = P (tt , (f x))
postPut : {a s : Set} {b : Set}
  -> (f : a -> s)
  -> (Q : Pair ⊤ s -> Pair b s -> Set)
  -> Pair a s -> Pair b s -> Set
postPut f Q (x , t) = Q (tt , (f x))

refineGet : {a s : Set} -> {b : Set}
  -> (P : Pair s s -> Set)
  -> (Q : Pair s s -> Pair b s -> Set)
  -> spec (preGet {a} P) (postGet {a} Q) ⊑ \x -> get >>= spec P Q
refineGet {a} {s} {b} P Q = refinement λ _ _ prf → prf
refinePut : {a s : Set} -> {b : Set}
  -> (P : Pair ⊤ s -> Set)
  -> (Q : Pair ⊤ s -> Pair b s -> Set)
  -> (t : a -> s)
  -> spec (prePut t P) (postPut t Q) ⊑ (\x -> put (t x) >>= spec P Q)
refinePut pre post t = refinement λ _ _ prf → prf

-- The type of all implementations of a given specification.
record Impl {a s : Set} {b : Set} (spec : a -> State s b) : Set where
  constructor impl
  field
    prog : a -> State s b
    code : (x : a) -> isCode (prog x)
    refines : spec ⊑ prog
open Impl

-- Combinators for 'easy' proofs of Impl.
doReturn : {a s : Set} ->
  {pre : Pair a s -> Set} ->
  {post : Pair a s -> Pair a s -> Set} ->
  (∀ i -> pre i -> post i i) ->
  Impl {a} {s} (spec pre post)
doReturn {a} {s} {pre} {post} prf = impl
  return
  (λ x → tt)
  (refinePrePost return (λ x → tt) pre post λ x t p → prf (x , t) p)

doGet : {a s : Set} -> {b : Set} ->
  {pre : Pair a s -> Set} ->
  {post : Pair a s -> Pair b s -> Set} ->
  (P : Pair s s -> Set) ->
  (Q : Pair s s -> Pair b s -> Set) ->
  (∀ i -> pre i -> preGet {a} P i) ->
  (∀ i o -> pre i -> postGet {a} Q i o -> post i o) ->
  (a -> Impl (spec P Q)) ->
  Impl (spec pre post)
doGet {a} {s} {b} {pre} {post} P Q sPre wPost cases = impl
  (\x -> get >>= prog (cases x))
  (λ x t → code (cases x) t)
  ((
    spec pre post
      ⟨ sharpenSpec pre (preGet P) post (postGet Q) sPre wPost ⟩
    spec (preGet P) (postGet Q)
      ⟨ refineGet P Q ⟩
    (\x -> get >>= spec P Q)
      ⟨ refineUnderGet (\x -> spec P Q) (\x -> prog (cases x)) (\x -> refines (cases x)) ⟩
    (\x -> get >>= prog (cases x)) ∎) pre-⊑)
  where
    refineUnderGet : {a s : Set} {b : Set} ->
      (prog prog' : a -> s -> State s b) ->
      ((x : a) -> prog x ⊑ prog' x) ->
      (\x -> get >>= prog x) ⊑ (\x -> get >>= prog' x)
    refineUnderGet prog prog' prf = refinement \P' i wpProg ->
      let (x , t) = i
      in holdsBind (P' (x , t)) get (prog' x) t (_⊑_.proof (prf x) (λ i → P' (x , t)) (t , t) wpProg)

doPut : {a s : Set} -> {b : Set} ->
  {pre : Pair a s -> Set} ->
  {post : Pair a s -> Pair b s -> Set} ->
  (f : a -> s)
  (P : Pair ⊤ s -> Set) ->
  (Q : Pair ⊤ s -> Pair b s -> Set) ->
  (∀ i -> pre i -> prePut f P i) ->
  (∀ i o -> pre i -> postPut f Q i o -> post i o) ->
  (a -> Impl (spec P Q)) ->
  Impl (spec pre post)
doPut {a} {s} {b} {pre} {post} f P Q st we cases = impl
  (\x -> put (f x) >>= prog (cases x))
  (λ x t → code (cases x) t)
  ((spec pre post
    ⟨ sharpenSpec pre (prePut f P) post (postPut f Q) st we ⟩
  spec (prePut f P) (postPut f Q)
    ⟨ refinePut P Q f ⟩
  ( \x -> put (f x) >>= spec P Q)
    ⟨ refineUnderPut f (\x -> spec P Q) (λ x → prog (cases x)) (λ x → refines (cases x)) ⟩
  ( (\x -> put (f x) >>= prog (cases x)) ∎)) pre-⊑)
  where
  refineUnderPut : {a s : Set} {b : Set} ->
    (f : a -> s) ->
    (prog prog' : a -> ⊤ -> State s b) ->
    ((x : a) -> prog x ⊑ prog' x) ->
    (\x -> put (f x) >>= prog x) ⊑ (\x -> put (f x) >>= prog' x)
  refineUnderPut f prog prog' prf = refinement \P' i wpProg
    -> let (x , t) = i
      in holdsBind (P' (x , t)) (put (f x)) (prog' x) t (_⊑_.proof (prf x) (λ x₁ → P' (x , t)) (tt , f x) wpProg)

-- Specify the incrementation program: give the current state and update it by incrementing.
incrPost : {t : Set} -> Pair t Nat -> Pair Nat Nat -> Set
incrPost (_ , n) (n' , n+1) = Pair (n == n') (Succ n == n+1)
incrSpec : ⊤ -> State Nat Nat
incrSpec = spec (\_ -> ⊤) incrPost

incrImpl : Impl incrSpec
incrImpl = doGet (\i -> Pair.fst i == Pair.snd i) (\i o -> Pair (Pair.fst i == Pair.fst o) (Succ (Pair.fst i) == Pair.snd o)) (λ i _ → Refl) (\i o _ post -> post)
  \_ -> doPut Succ {!!} (\i o -> Pair (Pair.snd i == Succ (Pair.fst o)) (Pair.snd i == Pair.snd o)) {!!} (\i o pre z -> succ-inj (Pair.fst z) , Pair.snd z)
  \n -> {!doReturn !}
