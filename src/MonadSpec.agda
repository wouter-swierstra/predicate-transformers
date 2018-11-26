{-# OPTIONS --type-in-type #-}
module MonadSpec where

open import Prelude
open import Preorder

Pre : (Set → Set) → Set
Pre m = m ⊤ → Set
Post : (Set → Set) → Set → Set
Post m a = m a → Set

data Mix (C : Set) (R : C → Set) (m : Set → Set) {{M : IsMonad m}} (a : Set) : Set where
  Pure : a → Mix C R m a -- or m a?
  Step : (c : C) → (k : R c → Mix C R m a) → Mix C R m a
  Spec : {a' : Set} → (pre : Pre m) → (post : Post m a') → (k : a' → m a) → Mix C R m a

spec : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a : Set} →
  (P : Pre m) (Q : Post m a) → Mix C R m a
spec {{M}} P Q = Spec P Q pure

instance
  IsMonadMix : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} → IsMonad (Mix C R m)
  IsMonadMix {C} {R} {m} {{M}} = isMonad _>>='_ Pure
    where
    _>>='_ : {a b : Set} → Mix C R m a → (a → Mix C R m b) → Mix C R m b
    Pure x >>=' f = f x
    Step c k >>=' f = Step c (λ z → k z >>=' f)
    Spec pre post k >>=' f = Spec pre post {!!}

isCode : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a : Set} → Mix C R m a → Set
isCode (Pure _) = ⊤
isCode {R = R} (Step c k) = (r : R c) → isCode (k r)
isCode (Spec _ _ _) = ⊥

run : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a : Set} →
  ((c : C) → m (R c)) →
  (prog : Mix C R m a) → isCode prog → m a
run h (Pure x) tt = pure x
run h (Step c k) ic = h c >>= λ r → run h (k r) (ic r)
run h (Spec pre post k) ()

wp : {a : Set} {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (pt : (c : C) → (R c → Pre m) → Pre m) →
  (Q : Post m a) →
  Mix C R m a → Pre m
wp {{M}} pt Q (Pure x) i = Q (i >> pure x)
wp {{M}} pt Q (Step c k) i = pt c (λ r o → wp pt Q (k r) o) i
wp {m = m} {{M}} pt Q (Spec {a'} pre post k) i = Pair (pre i) ((o : m a') → post (i >> o) → {!!} o)

-- A consistent set of axiomatic and operational semantics for a Mix.
record Semantics (C : Set) (R : C → Set) (m : Set → Set) {{M : IsMonad m}} : Set where
  constructor semantics
  field
    pt : (c : C) → (R c → Pre m) → Pre m
    handler : (c : C) → m (R c) -- The variable part of the runner.

    pt-if : (c : C) {P P' : R c → Pre m} →
      ((x : R c) (o : m ⊤) → P x o → P' x o) →
      (o : m ⊤) → pt c P o → pt c P' o
    lifter-bind : {a : Set} (P : Post m a) (c : C) (k : R c → m a) →
      (i : m ⊤) → pt c (λ r o → P (o >> k r)) i ⇔ P (i >> handler c >>= k)
open Semantics

pt-iff : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  (c : C) (P P' : R c → Pre m) →
  ((x : R c) (o : m ⊤) → P x o ⇔ P' x o) →
  (o : m ⊤) → pt s c P o ⇔ pt s c P' o
pt-iff s c P P' x o = iff
  (λ x₁ → pt-if s c (λ x₂ o₁ → _⇔_.if (x x₂ o₁)) o x₁)
  (λ x₁ → pt-if s c (λ x₂ o₁ → _⇔_.onlyIf (x x₂ o₁)) o x₁)

transformer : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  {a : Set} → Post m a → Mix C R m a → Pre m
transformer s = wp (pt s)

runner : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  {a : Set} → (p : Mix C R m a) → isCode p → m a
runner s = run (handler s)

consistent : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  {a : Set} → (P : Post m a) →
  (p : Mix C R m a) → (c : isCode p) →
  (i : m ⊤) → wp (pt s) P p i ⇔ P (i >> run (handler s) p c)
consistent s P (Pure x) tt i = ⇔-refl
consistent s P (Step c k) ic i = ⇔-trans (pt-iff s c _ (λ r o → P (o >> run (handler s) (k r) (ic r))) (λ r o → consistent s P (k r) (ic r) o) i )
  (lifter-bind s P c (λ r → run (handler s) (k r) (ic r)) i)
consistent s P (Spec pre post k) () i

record Refine {a : Set} {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}}
  (s : Semantics C R m) (p q : Mix C R m a) : Set where
  constructor refine
  field
    proof : ∀ (i : m ⊤) (P : Post m a) → transformer s P p i → transformer s P q i

pre-Refine : ∀ {a C R m} {{M : IsMonad m}} (s : Semantics C R m {{M}}) → Preorder (Refine {a} {C} {R} {m} {{M}} s)
pre-Refine {a} {C} {R} {m} s = Preorder.preorder (refine λ i P x → x) trans'
  where
  trans' : {x y z : Mix C R m a} → Refine s x y → Refine s y z → Refine s x z
  trans' (refine xy) (refine yz) = refine λ i P x → yz i P (xy i P x)

record Impl {a : Set} {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}}
  (s : Semantics C R m) (p : Mix C R m a) : Set where
  constructor impl
  field
    prog : Mix C R m a
    code : isCode prog
    refines : Refine s p prog

refine-itself : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a : Set} →
  (s : Semantics C R m) →
  (p : Mix C R m a) (c : isCode p) →
  (P : Pre m) (Q : Post m a) →
  ((i : m ⊤) → P i → Q (i >> run (handler s) p c)) →
  Refine s (spec P Q) p
refine-itself s@(semantics pt handler pt-if lifter-bind) p c P Q pf = refine λ i R x → _⇔_.if (consistent s R p c i) (let mx = i >> run handler p c in {!Pair.snd x!})

isCodeBind : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} →
  (mx : Mix C R m a) (f : a → Mix C R m b) →
  (cx : isCode mx) (cf : (x : a) → isCode (f x)) →
  isCode (mx >>= f)
isCodeBind (Pure x) f tt cf = cf x
isCodeBind (Step c k) f cx cf = λ r → isCodeBind (k r) f (cx r) cf
isCodeBind (Spec pre post k) f () cf

doReturn : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a : Set} →
  {s : Semantics C R m} →
  {P : Post m a} →
  (x : a) →
  Impl s (spec (λ i → P (i >> pure x)) P)
doReturn {C} {R} {m} {{M}} {a} {s} {P} x = impl (Pure x) tt (refine refines)
  where
  refines : ∀ (i : m ⊤) (P' : Post m a) →
    transformer s P' (spec (λ i → P (i >> pure x)) P) i →
    transformer s P' (Pure x) i
  refines i P' (fst , snd) = {!!}

doSharpen : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a : Set} →
  {s : Semantics C R m} →
  {P P' : Pre m} {Q Q' : Post m a} →
  ((i : m ⊤) → P' i → P i) → ((o : m a) → Q o → Q' o) →
  Impl s (spec P Q) → Impl s (spec P' Q')
doSharpen {C} {R} {m} {{M}} {a} {s} {P} {P'} {Q} {Q'} pre post (impl prog code (refine proof)) =
  impl prog code (refine refines)
  where
  refines : (i : m ⊤)
    (R : m a → Set) →
    transformer s R (spec P' Q') i →
    transformer s R prog i
  refines i R (fst , snd) = proof i R ((pre i fst) , {!!})

doBind : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} →
  {s : Semantics C R m} →
  {P1 : Pre m} {P2 : Post m a} {P3 : Post m b} →
  Impl s (spec P1 P2) → ((x : a) → Impl s (spec (λ i → P2 (i >> pure x)) P3)) →
  Impl s (spec P1 P3)
doBind {C} {R} {m} {{M}} {a} {b} {s} {P1} {P2} {P3} (impl prog code (refine proof)) f =
  impl (prog >>= prog') (isCodeBind prog prog' code code') (refine λ i P x → proof' {P3' = P} i prog (proof i P2 (Pair.fst x , {!!})) λ o x₁ x₂ → refine' x₁ o P (x₂ , {!!}))
  where
  prog' : (x : a) → Mix C R m b
  prog' x = Impl.prog (f x)
  code' : (x : a) → isCode (prog' x)
  code' x = Impl.code (f x)
  refine' : (x : a) → (i : m ⊤) (P : Post m b) → transformer s P (spec (λ i → P2 (i >> pure x)) P3) i → transformer s P (prog' x) i
  refine' x = Refine.proof (Impl.refines (f x))
  proof' : {P3' : Post m b} (i : m ⊤) (p : Mix C R m a) →
    transformer s P2 p i →
    ((o : m ⊤) (x : a) → P2 (o >> pure x) → transformer s P3' (prog' x) o) →
    transformer s P3' (p >>= prog') i
  proof' i (Pure x) pf2 pf3 = pf3 i x pf2
  proof' i (Step c k) pf2 pf3 = pt-if s c (λ x i' pf2' → proof' i' (k x) pf2' pf3) i pf2
  proof' i (Spec pre post k) (fst , snd) pf3 = fst , {!!}

doReturn' : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a : Set} →
  {s : Semantics C R m} →
  {P : Pre m} {Q : Post m a} →
  (x : a) → ((i : m ⊤) → P i → Q (i >> pure x)) →
  Impl s (spec P Q)
doReturn' {C} {R} {m} {{M}} {a} {s} {P} x pf = impl
  (Pure x)
  tt
  (refine λ i P₁ x₁ → {!!})
