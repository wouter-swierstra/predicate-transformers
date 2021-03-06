{-# OPTIONS --type-in-type #-}
module CombinedExamples where

open import Prelude
open import Data.Nat.Base
open import Combined
open import Maybe
open import Vector

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
State s = Free (EState s :: vNil)

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

-- Specify a computation that might fail.
wpFail : {a : Set} {n : Nat} →
  Free (ESpec :: EFail :: vNil) a → (P : a → Set) → Set
wpFail = WP.wp (es EFail ptFail :: vNil)
  where
  ptFail : PT EFail
  ptFail Fail wp _ = ⊥


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

-- Example: programs that can encounter an exception,
-- which is caught somewhere else.
module Exceptions where
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

  -- This is actually a bit hard to formulate concisely,
  -- but we want:
  -- if the try-part succeeds, then it should satisfy P,
  -- if the try-part fails, then the catch-part should satisfy P
  -- We can express this only if we can apply multiple conditions (i.e. successful termination) on the continuation!
  ptExcept : PT EExcept
  ptExcept Catch wp P = Pair
    (wp (const ⊤) Try → wp P Try)
    (¬ (wp (const ⊤) Try) → wp P Catch)
  ptFail : PT EFail
  ptFail Fail wp P = ⊥

  open WP (es EExcept ptExcept :: es EFail ptFail :: vNil)

  doFail : {a : Set} {P : Set} {Q : a → Set} →
    ¬ (terminates (spec P Q)) →
    Impl (spec P Q)
  doFail x = impl (Step (FS F0) Fail (λ ())) λ P x₁ → x (Pair.fst x₁ , (λ x₂ x₃ → tt))

  try_catch_[_,_] : {a : Set} {P P' P'' : Set} {Q Q' Q'' : a → Set} →
    (t : Impl (spec P' Q')) → (c : Impl (spec P'' Q'')) →
    (P → terminates (lift (Impl.prog t)) → wp (spec P' Q') Q) →
    (P → ¬ (terminates (lift (Impl.prog t))) → wp (spec P'' Q'') Q) →
    Impl (spec P Q)
  try impl t rt catch impl c rc [ ok , bad ] = impl (Step F0 Catch (caseRole t c)) λ P x → let
      p = Pair.fst x
    in (
      λ tryOK → rt P (Pair.fst (ok p tryOK) , λ x₁ x₂ → Pair.snd x x₁ (Pair.snd (ok p tryOK) x₁ x₂))) ,
      λ tryNo → rc P (Pair.fst (bad p tryNo) , λ x₁ x₂ → Pair.snd x x₁ (Pair.snd (bad p tryNo) x₁ x₂))
    where
    caseRole : {b : Set} (t c : b) → Role → b
    caseRole t _ Try = t
    caseRole _ c Catch = c

  slowProd : (xs : List Nat) → Nat
  slowProd Nil = 1
  slowProd (x :: xs) = x * slowProd xs

  isProd : (xs : List Nat) → (y : Nat) → Set
  isProd xs y = slowProd xs == y

  isProdZero : (xs : List Nat) → 0 ∈ xs → isProd xs 0
  isProdZero Nil ()
  isProdZero (.0 :: xs) ∈Head = refl
  isProdZero (x :: xs) (∈Tail i) = times-zero (slowProd xs) x (isProdZero xs i)
    where
    times-zero : (m n : Nat) → m == 0 → n * m == 0
    times-zero .0 zero refl = refl
    times-zero .0 (suc n) refl = times-zero 0 n refl

  -- Corresponds to the _;_ operator in GCL: if we have the intermediate
  -- as a postcondition for one program and precondition for the next,
  -- then we can sequence them.
  -- We need to be sure that the predicate transformer conserves implication.
  doBind : {a b : Set} {P1 : Set} {P2 : a → Set} {P3 : b → Set} →
    Impl (spec P1 P2) → ((x : a) → Impl (spec (P2 x) P3)) →
    Impl (spec P1 P3)
  doBind {a} {b} {P1} {P2} {P3} (impl prog1 refine1) t2 =
    impl (prog1 >>= prog2) (λ P x → wpBind prog1 prog2 (refine1 P2 (Pair.fst x , (λ x₁ x₂ → x₂))) λ x₁ x₂ → refine2 x₁ P (x₂ , (Pair.snd x)) )
    where
    prog2 : a → Free (EExcept :: EFail :: vNil) b
    prog2 x = Impl.prog (t2 x)
    refine2 : (x : a) → (P : b → Set) → wp (spec (P2 x) P3) P → wp (lift (prog2 x)) P
    refine2 x = Impl.refine (t2 x)
    wpBind : ∀ {a b} →
      {P2 : a → Set} {P3 : b → Set} →
      (t1 : Free (EExcept :: EFail :: vNil) a) (t2 : (x : a) → Free (EExcept :: EFail :: vNil) b) →
      wp (lift t1) P2 →
      ((x₁ : a) (x₂ : P2 x₁) → wp (lift (t2 x₁)) P3) →
      wp (lift (t1 >>= t2)) P3
    wpBind (Pure x) t2 p2 p3 = p3 x p2
    wpBind {a} {b} (Step F0 Catch k) t2 p2 p3 = (λ x → wpBind (k Try) t2 {!x!} {!!}) , λ x → wpBind (k Catch) t2 {!!} {!!}
    wpBind {a} {b} (Step (FS F0) Fail k) t2 p2 p3 = p2
    wpBind {a} {b} (Step (FS (FS ())) c k) t2 p2 p3

  fastProd : (xs : List Nat) → Impl (spec ⊤ (isProd xs))
  fastProd xs =
    try (go xs)
    catch (doReturn 0 (isProdZero xs))
    [ const (λ x → go-terminates xs x , λ x₁ x₂ → x₂) , const (λ x → go-diverges xs x , λ x₁ x₂ → x₂) ]
    where
    isProd-cons : (x p : Nat) (xs : List Nat) → isProd xs p → isProd (Cons x xs) (x * p)
    isProd-cons x .1 Nil refl = refl
    isProd-cons x .(x₂ * slowProd xs) (x₂ :: xs) refl = refl

    go : (xs : List Nat) → Impl (spec (¬ (0 ∈ xs)) (isProd xs))
    go Nil = doReturn 1 (const refl)
    go (zero :: xs) = doFail λ x → Pair.fst x ∈Head
    go (x@(suc _) :: xs) = doBind (doSharpen (λ z z₁ → z (∈Tail z₁)) (λ x₁ x₂ x₃ → x₃) (go xs)) λ prod → doReturn (x * prod) λ x₁ → isProd-cons x prod xs x₁

    ex-falso : {a : Set} → ⊥ → a
    ex-falso ()

    go-terminates : (xs : List Nat) → terminates (lift (Impl.prog (go xs))) → ¬ (0 ∈ xs)
    go-terminates Nil _ ()
    go-terminates (.0 :: xs) () ∈Head
    go-terminates (zero :: xs) () (∈Tail i)
    go-terminates ((suc x) :: xs) t (∈Tail i) = go-terminates xs {!!} i
    go-diverges : (xs : List Nat) → ¬ (terminates (lift (Impl.prog (go xs)))) → 0 ∈ xs
    go-diverges Nil x = ex-falso (x tt)
    go-diverges (zero :: xs) x = ∈Head
    go-diverges (suc x₁ :: xs) x = ∈Tail (go-diverges xs λ x₂ → x {!!})
