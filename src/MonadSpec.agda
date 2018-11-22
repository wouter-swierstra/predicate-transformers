{-# OPTIONS --type-in-type #-}
module MonadSpec where

open import Prelude

Pre : (Set → Set) → Set
Pre m = m ⊤ → Set
Post : (Set → Set) → Set → Set
Post m a = m a → Set

data Mix (C : Set) (R : C → Set) (m : Set → Set) {{M : IsMonad m}} (a : Set) : Set where
  Pure : a → Mix C R m a -- or m a?
  Step : (c : C) → (k : R c → Mix C R m a) → Mix C R m a
  Spec : {a' : Set} → (pre : Pre m) → (post : Post m a') → (k : a' → Mix C R m a) → Mix C R m a

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
wp {m = m} {{M}} pt Q (Spec {a'} pre post k) i = Pair (pre i) ((o : m ⊤) (x : a') → post (o >> pure x) → wp pt Q (k x) o)

-- A consistent set of axiomatic and operational semantics for a Mix.
record Semantics (C : Set) (R : C → Set) (m : Set → Set) {{M : IsMonad m}} : Set where
  constructor semantics
  field
    pt : (c : C) → (R c → Pre m) → Pre m
    handler : (c : C) → m (R c) -- The variable part of the runner.

    pt-if : (c : C) (P P' : R c → Pre m) →
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
  (λ x₁ → pt-if s c P' P (λ x₂ o₁ → _⇔_.if (x x₂ o₁)) o x₁)
  (λ x₁ → pt-if s c P P' (λ x₂ o₁ → _⇔_.onlyIf (x x₂ o₁)) o x₁)

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
