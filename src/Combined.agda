{-# OPTIONS --type-in-type #-}

module Combined where

open import Data.Nat.Base
open import Prelude hiding (_++_)
open import Maybe
open import Vector

Effect : Set
Effect = Sigma Set (λ C → (C → Set))

C : Effect → Set
C = Sigma.fst
R : (e : Effect) → C e → Set
R = Sigma.snd

data Free {n : Nat} (Cs : Vec n Effect) (a : Set) : Set where
  Pure : a → Free Cs a
  Step : (i : Fin n) (c : C (Cs !! i)) → (k : R (Cs !! i) c → Free Cs a) → Free Cs a

_++_ : {k n : Nat} {a : Set} → Vec k a → Vec n a → Vec (k + n) a
vNil ++ ys = ys
vCons x xs ++ ys = vCons x (xs ++ ys)

Handler : (m : Set → Set) → Effect → Set
Handler m (C , R) = {a : Set} → (c : C) → (k : R c → m a) → m a
record EffectHandler (m : Set → Set) : Set where
  constructor eh
  field
    e : Effect
    h : Handler m e

handle : ∀ {n m} (es : Vec n (EffectHandler m)) →
  (i : Fin n) → Handler m ((vmap EffectHandler.e es) !! i)
handle vNil ()
handle (vCons (eh e h) es) F0 c = h c
handle (vCons e es) (FS i) c = handle es i c

run : {m : Set → Set} {{M : IsMonad m}} →
  {n : Nat} {es : Vec n Effect} {a : Set} →
  (h : (i : Fin n) → Handler m (es !! i)) →
  Free es a → m a
run h (Pure x) = pure x
run h (Step i c k) = h i c (λ x → run h (k x))

run' : {m : Set → Set} {{M : IsMonad m}} →
  {n : Nat} (es : Vec n (EffectHandler m)) {a : Set} →
  Free (vmap EffectHandler.e es) a → m a
run' es x = run (handle es) x


-- Example: Identity
Identity : Set → Set
Identity = Free vNil


-- Example: State
data CState (s : Set) : Set where
  Get : CState s
  Put : s → CState s

RState : (s : Set) → CState s → Set
RState s Get = s
RState s (Put x) = ⊤

EState : (s : Set) → Effect
EState s = CState s , RState s
State : (s : Set) → Set → Set
State s = Free (vCons (EState s) vNil)

runState : {s a : Set} →
  State s a → s → Pair a s
runState {s} x i = run' {{StateMonad}} (eh (EState s) hState :: vNil) x i
  where
  StateMonad : IsMonad (λ a → s → Pair a s)
  IsMonad.bind StateMonad mx f t = uncurry f (mx t)
  IsMonad.pure StateMonad = _,_
  IsMonad.left-identity StateMonad = refl

  hState : Handler (λ a → s → Pair a s) (EState s)
  hState Get k t = k t t
  hState (Put t') k t = k tt t'

data CFail : Set where
  Fail : CFail
RFail : CFail → Set
RFail Fail = ⊥
EFail : Effect
EFail = CFail , RFail

-- Run, resetting the state on failure.
runReset : {s a : Set} → Free (EState s :: EFail :: vNil) a →
  s → Maybe (Pair a s)
runReset {s} = run' {{MonadReset}}
  (eh (EState s) hState :: eh EFail hFail :: vNil)
  where
  reset : Set → Set
  reset a = s → Maybe (Pair a s)
  MonadReset : IsMonad reset
  IsMonad.bind MonadReset mx f t with mx t
  IsMonad.bind MonadReset mx f t | Just x = uncurry f x
  IsMonad.bind MonadReset mx f t | Nothing = Nothing
  IsMonad.pure MonadReset x t = Just (x , t)
  IsMonad.left-identity MonadReset = refl

  hState : Handler reset (EState s)
  hState Get k t = k t t
  hState (Put t') k t = k tt t'
  hFail : Handler reset EFail
  hFail Fail k t = Nothing
-- Run, preserving the state on failure.
runPreserve : {s a : Set} → Free (EState s :: EFail :: vNil) a →
  s → Pair (Maybe a) s
runPreserve {s} = run' {{MonadPreserve}}
  (eh (EState s) hState :: eh EFail hFail :: vNil)
  where
  preserve : Set → Set
  preserve a = s → Pair (Maybe a) s
  MonadPreserve : IsMonad preserve
  IsMonad.bind MonadPreserve mx f t with mx t
  IsMonad.bind MonadPreserve mx f t | Just x , t' = f x t'
  IsMonad.bind MonadPreserve mx f t | Nothing , t' = Nothing , t'
  IsMonad.pure MonadPreserve x t = Just x , t
  IsMonad.left-identity MonadPreserve = refl

  hState : Handler preserve (EState s)
  hState Get k t = k t t
  hState (Put t') k t = k tt t'
  hFail : Handler preserve EFail
  hFail Fail k t = Nothing , t


data CSpec : Set where
  Spec : {a : Set} (pre : Set) → (post : a → Set) → CSpec
RSpec : CSpec → Set
RSpec (Spec {a} _ _) = a
ESpec : Effect
ESpec = CSpec , RSpec

record EffectSpec : Set where
  constructor es
  field
    e : Effect
    s : (c : Sigma.fst e) → (P : Sigma.snd e c → Set) → Set
effects' : {n : Nat} → Vec n EffectSpec → Vec n Effect
effects' = vmap (EffectSpec.e)

-- It's nicer for the user to pass in a list of handlers,
-- but it's nicer for wp to use indexing.
-- When we index in this list, we have to prove that we have a correct pt,
-- so that's why we have this helper function.
pt : {n : Nat} (es : Vec n EffectSpec) (i : Fin n) →
  Sigma (C (effects' es !! i)) (λ c → R (effects' es !! i) c → Set) → Set
pt ES i cr = let
    cr' = coerce (cong (λ x → Sigma (C x) (λ c → R x c → Set))
      (index-map i EffectSpec.e ES)) cr
  in EffectSpec.s (ES !! i) (Sigma.fst cr') (Sigma.snd cr')

wp : {a : Set} {n : Nat} → (es : Vec n EffectSpec) → Free (ESpec :: effects' es) a → (P : a → Set) → Set
wp ES (Pure x) P = P x
wp ES (Step F0 (Spec {a'} pre post) k) P = Pair pre ((x : a') → post x → wp ES (k x) P)
wp ES (Step (FS i) c k) P = pt ES i (c , λ x → wp ES (k x) P)


-- Specify a computation that might fail.
wpFail : {a : Set} {n : Nat} →
  Free (ESpec :: EFail :: vNil) a → (P : a → Set) → Set
wpFail = wp (es EFail ptFail :: vNil)
  where
  ptFail : (c : CFail) → (P : RFail c → Set) → Set
  ptFail Fail P = ⊥


-- We can also incorporate state into our specifications:
data CStateSpec (s : Set) : Set where
  Spec : {a : Set} (pre : s → Set) → (post : s → a → s → Set) → CStateSpec s
RStateSpec : (s : Set) → CStateSpec s → Set
RStateSpec s (Spec {a} _ _) = a
EStateSpec : (s : Set) → Effect
EStateSpec s = CStateSpec s , RStateSpec s

record EffectStateSpec (s : Set) : Set where
  constructor es
  field
    e : Effect
    p : (c : Sigma.fst e) → (P : Sigma.snd e c → s → Set) → s → Set
effects'' : {s : Set} {n : Nat} → Vec n (EffectStateSpec s) → Vec n Effect
effects'' = vmap (EffectStateSpec.e)

pt' : {s : Set} {n : Nat} (es : Vec n (EffectStateSpec s)) (i : Fin n) →
  Sigma (C (effects'' es !! i)) (λ c → R (effects'' es !! i) c → s → Set) → s → Set
pt' {s} ES i cr t = let
    cr' = coerce (cong (λ x → Sigma (C x) (λ c → R x c → s → Set))
      (index-map i EffectStateSpec.e ES)) cr
  in EffectStateSpec.p (ES !! i) (Sigma.fst cr') (Sigma.snd cr') t

wpState : {s a : Set} {n : Nat} → (es : Vec n (EffectStateSpec s)) →
  Free (EStateSpec s :: effects'' es) a → (P : a → s → Set) → s → Set
wpState ES (Pure x) P t =
  P x t
wpState {s} ES (Step F0 (Spec {a'} pre post) k) P t =
  Pair (pre t) ((x : a') (o : s) → post t x o → wpState ES (k x) P o)
wpState ES (Step (FS i) c k) P t =
  pt' ES i (c , λ x → wpState ES (k x) P) t


wpReset : {s a : Set} → Free (EStateSpec s :: EState s :: EFail :: vNil) a →
  (P : a → s → Set) → s → Set
wpReset {s} = wpState (es (EState s) ptState :: es EFail ptFail :: vNil)
  where
  ptState : (c : CState s) → (P : RState s c → s → Set) → s → Set
  ptState Get P t = P t t
  ptState (Put t') P t = P tt t'
  ptFail : (c : CFail) → (P : RFail c → s → Set) → s → Set
  ptFail Fail P t = ⊥

-- This can't really give another semantics since fail must give ⊥ in wp!
-- Can we still say something about the state though?
wpPreserve : {s a : Set} → Free (EStateSpec s :: EState s :: EFail :: vNil) a →
  (P : a → s → Set) → s → Set
wpPreserve {s} = wpState (es (EState s) ptState :: es EFail ptFail :: vNil)
  where
  ptState : (c : CState s) → (P : RState s c → s → Set) → s → Set
  ptState Get P t = P t t
  ptState (Put t') P t = P tt t'
  ptFail : (c : CFail) → (P : RFail c → s → Set) → s → Set
  ptFail Fail P t = {!!}

-- We want two continuations under Catch,
-- so indicate which of the two using its Role.
data Role : Set where
  Try : Role
  Catch : Role
data CExcept : Set where
  Catch : CExcept
RExcept : CExcept → Set
RExcept Catch = Role
EExcept : Effect
EExcept = CExcept , RExcept

runExcept : {a : Set} → Free (EExcept :: EFail :: vNil) a → Maybe a
runExcept = run' (eh EExcept hCatch :: eh EFail hFail :: vNil)
  where
  hFail : Handler Maybe EFail
  hFail Fail k = Nothing
  hCatch : Handler Maybe EExcept
  hCatch Catch k with k Try
  ... | Just x = Just x
  ... | Nothing = k Catch

wpExcept : {a : Set} → Free (ESpec :: EExcept :: EFail :: vNil) a → (P : a → Set) → Set
wpExcept = wp (es _ ptExcept :: es _ ptFail :: vNil)
  where
  -- This is actually a bit hard to formulate concisely,
  -- but we want:
  -- if the try-part fails, then the catch-part should satisfy P
  -- otherwise the try-part should satisfy P.
  -- We can express this only if we can apply arbitrary conditions on the continuation!
  ptExcept : (c : CExcept) → (RExcept c → Set) → Set
  ptExcept Catch P = 
  ptFail : (c : CFail) → (RFail c → Set) → Set
  ptFail Fail P = ⊥
