{-# OPTIONS --type-in-type #-}

module Combined where

open import Prelude hiding (_++_)
open import Data.Nat.Base using (_+_)
open import Vector public

Effect : Set
Effect = Sigma Set (λ C → (C → Set))

C : Effect → Set
C = Sigma.fst
R : (e : Effect) → C e → Set
R = Sigma.snd

data Free {n : Nat} (Cs : Vec n Effect) (a : Set) : Set where
  Pure : a → Free Cs a
  Step : (i : Fin n) (c : C (Cs !! i)) → (k : R (Cs !! i) c → Free Cs a) → Free Cs a

instance
  IsMonad-Free : {n : Nat} {Cs : Vec n Effect} → IsMonad (Free Cs)
  IsMonad-Free {n} {Cs} = isMonad b Pure refl rid
    where
    b : {a : Set} {b : Set} → Free Cs a → (a → Free Cs b) → Free Cs b
    b (Pure x) f = f x
    b (Step i c k) f = Step i c (λ z → b (k z) f)

    rid : {a : Set} {mx : Free Cs a} → b mx Pure == mx
    rid {a} {Pure x} = refl
    rid {a} {Step i c k} = cong (Step i c) (extensionality λ x → rid)

_++_ : {k n : Nat} {a : Set} → Vec k a → Vec n a → Vec (k + n) a
vNil ++ ys = ys
(x :: xs) ++ ys = vCons x (xs ++ ys)

-- Add additional potential effects (that we will not use).
lift : {n : Nat} {a : Set} {e : Effect} {es : Vec n Effect} →
  Free es a → Free (e :: es) a
lift (Pure x) = Pure x
lift (Step i c k) = Step (FS i) c (λ z → lift (k z))

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
handle ((eh e h) :: es) F0 c = h c
handle (e :: es) (FS i) c = handle es i c

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

-- Now we can "really" view Spec as an effect.
data CSpec : Set where
  Spec : {a : Set} (pre : Set) → (post : a → Set) → CSpec
RSpec : CSpec → Set
RSpec (Spec {a} _ _) = a
ESpec : Effect
ESpec = CSpec , RSpec

PT : (e : Effect) → Set
PT (C , R) = (c : C) (wp : R c → Set) → Set
record EffectSpec : Set where
  constructor es
  field
    e : Effect
    s : PT e

effects' : {n : Nat} → Vec n EffectSpec → Vec n Effect
effects' = vmap (EffectSpec.e)

module WP {n : Nat} (ES : Vec n EffectSpec) where
  -- It's nicer for the user to pass in a list of handlers,
  -- but it's nicer for wp to use indexing.
  -- When we index in this list, we have to prove that we have a correct pt,
  -- so that's why we have this helper function.
  pt : (i : Fin n) →
    Sigma (C (effects' ES !! i)) (λ c → (R (effects' ES !! i) c) → Set) → Set
  pt i cr = let
      cr' = coerce (cong (λ e → Sigma (C e) λ c → R e c → Set)
        (index-map i EffectSpec.e ES)) cr
    in EffectSpec.s (ES !! i) (Sigma.fst cr') (Sigma.snd cr')

  wp : {a : Set}  → Free (ESpec :: effects' ES) a → (P : a → Set) → Set
  wp (Pure x) P = P x
  wp (Step F0 (Spec {a'} pre post) k) P = Pair pre ((x : a') → post x → wp (k x) P)
  wp (Step (FS i) c k) P = pt i (c , λ x → wp (k x) P)

  terminates : {a : Set} → Free (ESpec :: effects' ES) a → Set
  terminates = flip wp (const ⊤)

  record Impl {a : Set} (p : Free (ESpec :: effects' ES) a) : Set where
    constructor impl
    field
      prog : Free (effects' ES) a
      refine : (P : a → Set) → wp p P → wp (lift prog) P

  spec : {a : Set} →
    (P : Set) (Q : a → Set) →
    Free (ESpec :: effects' ES) a
  spec P Q = Step F0 (Spec P Q) Pure

  doReturn : {a : Set} →
    {P : Set} {Q : a → Set} →
    (x : a) → (P → Q x) →
    Impl (spec P Q)
  doReturn x pf = impl (Pure x) (λ P z → Pair.snd z x (pf (Pair.fst z)))

  doSharpen : {a : Set} →
    {P P' : Set} {Q Q' : a → Set} →
    (P → P') → ((x : a) → (P → Q' x → Q x)) →
    Impl (spec P' Q') → Impl (spec P Q)
  doSharpen pre post (impl prog refine) = impl prog (λ P z → refine P (pre (Pair.fst z) , (λ x x₁ → Pair.snd z x (post x (Pair.fst z) x₁))))

  wp-bind : ∀ {a b} →
    (ptC : ∀ i c P Q → (∀ x → P x → Q x) → pt i (c , P) → pt i (c , Q)) →
    ∀ P (p : Free (ESpec :: effects' ES) a) →
    ∀ Q (q : a → Free (ESpec :: effects' ES) b) →
    wp p P → ((x : a) → P x → wp (q x) Q) →
    wp (p >>= q) Q
  wp-bind ptC P (Pure x) Q q wp-p wp-q = wp-q x wp-p
  wp-bind ptC P (Step F0 (Spec pre post) k) Q q (fst , snd) wp-q =
    fst , λ x x₁ → wp-bind ptC P (k x) Q q (snd x x₁) wp-q
  wp-bind ptC P (Step (FS i) c k) Q q wp-p wp-q =
    ptC i c (λ x → wp (k x) P) (λ x → wp (k x >>= q) Q)
      (λ x z → wp-bind ptC P (k x) Q q z wp-q) wp-p
