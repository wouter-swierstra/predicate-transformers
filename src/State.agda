{-# OPTIONS --type-in-type #-}

open import Prelude
open import Maybe

open import Preorder
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
  -> (x : Pair ⊤ s)
  -> (prog : State s a) -> Set
holds P (_ , t) (Pure x) = P (x , t)
holds P (_ , t) (Step Get k) = holds P (tt , t) (k t)
holds P (_ , t) (Step (Put x) k) = holds P (tt , x) (k tt)
holds {s = s} P (_ , t) (Spec {b} pre post k) = Pair (pre ⊤ (tt , t)) -- if precondition holds
  ((x : b) -> (t' : s) -> post ⊤ (tt , t) (x , t') -- and for all intermediate values such that the postcondition holds,
    -> holds P (tt , t') (k x)) -- then the continuation makes P hold

wpState : {a s : Set} -> {b : a -> Set}
  -> (P : Post (rtState s) a b)
  -> (f : (x : a) -> State s (b x))
  -> (Pre (rtState s) a)
wpState P f (x , t) = wp (\y -> holds (P (y , t)) (tt , t)) f x

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
    proof : (∀ P -> wpState P f ⊆ wpState P g)

pre-⊑ : ∀ {a b c} -> Preorder (_⊑_ {a} {b} {c})
pre-⊑ = preorder
  (refinement (λ P x₁ z → z))
  (λ p q → refinement (λ P x₁ z₁ → _⊑_.proof q P x₁ (_⊑_.proof p P x₁ z₁)))

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
    -> (t : s) -> holds P (tt , t) prog -> P (runState prog prf t)
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
  -> holds post (tt , t) prog
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
      -> (x : a) -> (t : s) -> holds P (tt , t) (spec (\i -> pre (Pair.fst i)) (\i -> post (Pair.fst i)) t)
      -> holds P (tt , t) prog
    rPP' prog prf pre post postAfterRun P x t (preHolds , postImpliesP)
      = let (y , t') = runState prog prf t
        in completeness' prog prf pre P t preHolds
            (postImpliesP y t' (postAfterRun t preHolds))
    prePost : (P : Pair a s -> Pair b s -> Set) -> (x : Pair a s) -> wpState P (spec pre post) x -> wpState P prog x
    prePost P (x , t) wpSpec = rPP' (prog x) (prf x) (λ z → pre (x , z)) (\z -> post (x , z)) (postAfterRun x) (P (x , t)) x t wpSpec
