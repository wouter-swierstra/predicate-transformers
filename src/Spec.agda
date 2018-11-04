{-# OPTIONS --type-in-type #-}
module Spec where
import Free
open import Prelude hiding (_⟨_⟩_)
open import Maybe
open import Preorder

open Preorder.Preorder
open IsMonad

Pre : Set -> Set
Pre a = a -> Set
Post : (a : Set) -> (a -> Set) -> Set
Post a b = (x : a) -> b x -> Set

-- Mix code with specifications.
data Mix (C : Set) (R : C -> Set) (a : Set) : Set where
  Pure : a -> Mix C R a
  Step : (c : C) -> (k : R c -> Mix C R a) -> Mix C R a
  Spec : {a' : Set}
    -> Set
    -> (a' -> Set)
    -> (k : a' -> Mix C R a) -> Mix C R a

infixl 20 _>>=_
_>>=_ : {C : Set} {R : C -> Set} -> {a : Set} {b : Set}
  -> Mix C R a -> (a -> Mix C R b) -> Mix C R b
Pure x >>= f = f x
Step c k >>= f = Step c (λ z → k z >>= f)
Spec pre post k >>= f = Spec pre post (λ z → k z >>= f)

fromCode : {C : Set} {R : C -> Set} {a : Set}
  -> Free.Free C R a -> Mix C R a
fromCode (Free.Pure x) = Pure x
fromCode (Free.Step c x) = Step c (λ z → fromCode (x z))

return : {a : Set}
  {C : Set} {R : C -> Set}
  -> a -> Mix C R a
return x = Pure x
spec : {bx : Set} {C : Set} {R : C -> Set}
  -> (P : Set)
  -> (Q : bx -> Set)
  -> Mix C R bx
spec {a} {b} P Q = Spec P Q Pure

-- The type of functions that convert pure postconditions
-- to ones about effects.
PTs : (C : Set) (R : C -> Set) -> Set
PTs C R = (c : C) -> (P : R c -> Set) -> Set

-- Given a semantics, decide whether the postcondition holds afterwards.
wpMix : {C : Set} {R : C -> Set} {bx : Set}
  -> PTs C R
  -> (P : bx -> Set)
  -> Mix C R bx -> Set
wpMix PT P (Pure y) = P y
wpMix PT P (Step c k) = PT c (\r -> wpMix PT P (k r))
wpMix PT P (Spec {c} pre post k) = Pair pre -- if the precondition holds
  ((z : c) -- and for all intermediate values
    -> post z -- such that the postcondition holds
    -> wpMix PT P (k z)) -- then the continuation makes P hold

-- The weakest precondition for a monadic function.
isCode : {C : Set} {R : C -> Set}
  -> {a : Set} -> Mix C R a -> Set
isCode (Pure _) = ⊤
isCode {R = R} (Step c k) = (x : R c) -> isCode (k x)
isCode (Spec _ _ _) = ⊥

isCodeBind :  {C : Set} {R : C -> Set} ->
  {a : Set} {b : Set} ->
  (mx : Mix C R a) -> (f : a -> Mix C R b) ->
  isCode mx -> ((x : a) -> isCode (f x)) ->
  isCode (mx >>= f)
isCodeBind (Pure x) f mxisC fisC = fisC x
isCodeBind (Step c k) f mxisC fisC x = isCodeBind (k x) f (mxisC x) fisC
isCodeBind (Spec pre post k) f ()

run : {C : Set} {R : C -> Set}
  -> {tyO : Set -> Set} -> IsMonad tyO -> (handler : (c : C) -> tyO (R c))
  -> {a : Set} -> (prog : Mix C R a) -> isCode prog
  -> tyO a
run m h (Pure out) prf = pure m out
run m h (Step c k) prf = bind m (h c) \int -> run m h (k int) (prf int)
run _ _ (Spec _ _ _) ()

-- The refinement relation, parametrized over the predicate transformer.
record Refine {C : Set} {R : C -> Set} (PT : PTs C R)
  {bx : Set} (f g : Mix C R bx) : Set₁ where
  constructor refinement
  field
    proof : (P : bx -> Set) -> wpMix PT P f -> wpMix PT P g
pre-Refine : {bx : Set} {C : Set} {R : C -> Set} {PT : PTs C R} -> Preorder (Refine PT {bx = bx})
Refine.proof (pre-refl pre-Refine) _ prf = prf
Refine.proof (pre-trans pre-Refine (refinement fg) (refinement gh)) P prf = gh P (fg P prf)

-- A consistent set of axiomatic and operational semantics for a Mix.
record Semantics (C : Set) (R : C → Set) {m : Set → Set} (M : IsMonad m) : Set where
  constructor semantics
  field
    lifter : {a : Set} → (a → Set) → (m a → Set)
    pt : PTs C R -- The variable part of the transformer.
    handler : (c : C) → m (R c) -- The variable part of the runner.

    lifter-pure : {a : Set} → (P : a → Set) → (x : a) →
      P x ⇔ lifter P (IsMonad.pure M x)
    pt-iff : (c : C) (P P' : R c → Set) → ((x : R c) → P x ⇔ P' x) →
      pt c P ⇔ pt c P'
    lifter-bind : {a : Set} (P : a → Set) (c : C) (k : R c → m a) →
      pt c (λ x → lifter P (k x)) ⇔ lifter P (IsMonad.bind M (handler c) k)
open Semantics

transformer : {C : Set} {R : C → Set} {m : Set → Set} {M : IsMonad m} →
  (s : Semantics C R M) →
  {a : Set} → (a → Set) → (Mix C R a → Set)
transformer s = wpMix (pt s)

runner : {C : Set} {R : C → Set} {m : Set → Set} {M : IsMonad m} →
  (s : Semantics C R M) →
  {a : Set} → (p : Mix C R a) → isCode p → m a
runner {M = M} s = run M (handler s)

consistent : {C : Set} {R : C → Set} {m : Set → Set} {M : IsMonad m} →
  (s : Semantics C R M) →
  {a : Set} → (P : a → Set) →
  (p : Mix C R a) → (c : isCode p) →
  transformer s P p ⇔ lifter s P (runner s p c)
consistent s P (Pure x₁) c = lifter-pure s P x₁
consistent s P (Step c k) ic = ⇔-trans
  (pt-iff s c _ (λ x → lifter s P (runner s (k x) (ic x)))
    λ x → consistent s P (k x) (ic x))
  (lifter-bind s P c λ x → runner s (k x) (ic x))
consistent s P (Spec _ _ _) ()

sharpenSpec : {b : Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  {pre pre' : Set} ->
  {post post' : b -> Set} ->
  (pre -> pre') ->
  (∀ o -> pre -> post' o -> post o) ->
  Refine PT (spec pre post) (spec pre' post')
sharpenSpec {a} {s} {b} {pre} {pre'} {post} {post'} sh we
  = refinement λ P x → sh (Pair.fst x) , (λ x₁ x₂ → Pair.snd x x₁ (we x₁ (Pair.fst x) x₂))

-- Give an implementation of an (abstract) program, and proof of this fact.
record Impl {C : Set} {R : C -> Set} (PT : PTs C R)
  {bx : Set} (spec : Mix C R bx) : Set₁ where
  constructor impl
  field
    prog : Mix C R bx
    code : isCode prog
    refines : Refine PT spec prog

doSharpen' : {a : Set}
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  {pre pre' : Set} ->
  {post post' : a -> Set} ->
  ((P : a -> Set) -> Pair pre ((z : a) -> post z -> P z) -> (Pair pre' ((z : a) -> post' z -> P z))) ->
  Impl PT (spec pre' post') ->
  Impl PT (spec pre post)
Impl.prog (doSharpen' {a} {s} {C} {R} {PT} {pre} _ (impl prog₁ code₁ (refinement proof))) = prog₁
Impl.code (doSharpen' {a} {s} {C} {R} {PT} {pre} _ (impl prog₁ code₁ (refinement proof))) = code₁
Refine.proof (Impl.refines (doSharpen' {a} {C} {R} {PT} {pre} {pre'} {post} {post'} proof' (impl prog₁ code₁ (refinement proof)))) P x = proof P ((¹ (proof' P x)) , λ z x₁ → Pair.snd (proof' P x) z x₁)

doReturn : {bx : Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  {pre : Set} {post : bx -> Set} ->
  (y : bx) -> (pre -> post y) ->
  Impl PT (spec pre post)
doReturn {a} {s} y prf = impl
  (return y)
  tt
  (refinement (λ P z → Pair.snd z y (prf (Pair.fst z))))

doReturn' : {a : Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  (post : a -> Set) ->
  (x : a) -> Impl PT (spec (post x) post)
doReturn' {a} {s} post x = impl
  (return x)
  tt
  (refinement (λ P z → Pair.snd z x (Pair.fst z)))

doIgnorePre : {a : Set} ->
  {C : Set} {R : C -> Set} {PT : PTs C R} ->
  {pre : Set} {post : a -> Set} ->
  Impl PT (spec ⊤ (\x -> pre -> post x)) -> Impl PT (spec pre post)
doIgnorePre x = doSharpen' (λ P x₁ → tt , (λ x₂ x₃ → Pair.snd x₁ x₂ (x₃ (Pair.fst x₁)))) x

wpBind : {C : Set} {R : C -> Set} {PT : PTs C R} →
  ((c : C) → {P P' : R c → Set} → ((x : R c) → P x → P' x) → PT c P → PT c P') →
  {a b : Set} {P2 : a → Set} {P3 : b → Set} →
  {t1 : Mix C R a} {t2 : a → Mix C R b} →
  wpMix PT P2 t1 → ((x : a) → P2 x → wpMix PT P3 (t2 x)) →
  wpMix PT P3 (t1 >>= t2)
wpBind {C} {R} {PT} cPT {a} {b} {P2} {P3} {Pure x} {t2} wp1 wp2 = wp2 x wp1
wpBind {C} {R} {PT} cPT {a} {b} {P2} {P3} {Step c k} {t2} wp1 wp2 =
  cPT c (λ x wp1' → wpBind cPT {t1 = k x} wp1' wp2) wp1
wpBind {C} {R} {PT} cPT {a} {b} {P2} {P3} {Spec pre post k} {t2} (fst , snd) wp2 =
  fst , λ z x₂ → wpBind cPT {t1 = k z} (snd z x₂) wp2

-- Corresponds to the _;_ operator in GCL: if we have the intermediate
-- as a postcondition for one program and precondition for the next,
-- then we can sequence them.
-- We need to be sure that the predicate transformer conserves implication.
doBind : {C : Set} {R : C -> Set} {PT : PTs C R} →
  ((c : C) → {P P' : R c → Set} → ((x : R c) → P x → P' x) → PT c P → PT c P') →
  {a b : Set} {P1 : Set} {P2 : a → Set} {P3 : b → Set} →
  Impl PT (spec P1 P2) → ((x : a) → Impl PT (spec (P2 x) P3)) →
  Impl PT (spec P1 P3)
doBind {C} {R} {PT} cPT {a} {b} {P1} {P2} {P3} (impl prog1 code1 (refinement wp1)) t2 =
  impl (prog1 >>= prog2) (isCodeBind _ _ code1 code2) (refinement λ P x → wpBind cPT {t1 = prog1} (wp1 P2 (Pair.fst x , (λ x₁ x₂ → x₂))) λ x₁ x₂ → wp2 x₁ P (x₂ , (Pair.snd x)))
  where
  prog2 : a → Mix C R b
  prog2 x = Impl.prog (t2 x)
  code2 : (x : a) → isCode (prog2 x)
  code2 x = Impl.code (t2 x)
  refines2 : (x : a) → Refine PT (spec (P2 x) P3) (prog2 x)
  refines2 x = Impl.refines (t2 x)
  wp2 : (x : a) → (P : b → Set) → wpMix PT P (spec (P2 x) P3) → wpMix PT P (prog2 x)
  wp2 x = Refine.proof (refines2 x)
