{-# OPTIONS --type-in-type #-}
module MonadSpec where

open import Prelude
open import Preorder

Pre : (m : Set → Set) (a : Set) → Set
Pre m a = m a → Set
Post : (Set → Set) → (a b : Set) → Set
Post m a b = m a → m b → Set

data Mix (C : Set) (R : C → Set) (m : Set → Set) {{M : IsMonad m}} (a b : Set) : Set where
  Pure : (f : a → b) → Mix C R m a b -- or a → m b?
  Step : (k : a → Sigma C λ c → Mix C R m (R c) b) → Mix C R m a b
  Spec : {a' : Set} → (pre : Pre m a) → (post : Post m a a') → (k : Mix C R m a' b) → Mix C R m a b

spec : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} →
  (P : Pre m a) (Q : Post m a b) → Mix C R m a b
spec {{M}} P Q = Spec P Q (Pure id)

_>=>_ : ∀ {C R m a b c} {{M : IsMonad m}} → Mix C R m a b → Mix C R m b c → Mix C R m a c
Pure f >=> Pure g = Pure (g ∘ f)
Pure f >=> Step k = Step (k ∘ f)
Pure f >=> Spec pre post g = Spec (pre ∘ fmap f) (post ∘ fmap f) g
Step k >=> g = Step λ x → Sigma.fst (k x) , (Sigma.snd (k x) >=> g)
Spec pre post f >=> g = Spec pre post (f >=> g)

isCode : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} → Mix C R m a b → Set
isCode (Pure _) = ⊤
isCode {R = R} {a = a} (Step k) = (x : a) → isCode (Sigma.snd (k x))
isCode (Spec _ _ _) = ⊥

run : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} →
  ((c : C) → m (R c)) →
  (prog : Mix C R m a b) → isCode prog → a → m b
run h (Pure f) tt x = pure (f x)
run h (Step k) ic x = h (Sigma.fst (k x)) >>= run h (Sigma.snd (k x)) (ic x)
run h (Spec pre post k) ()

wp : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (pt : {a : Set} → (a → Sigma C λ c → Pre m (R c)) → Pre m a) →
  {a b : Set} →
  (Q : m b → Set) →
  Mix C R m a b → Pre m a
wp {{M}} pt Q (Pure f) i = Q (fmap f i)
wp {{M}} pt Q (Step k) i = pt (λ x → Sigma.fst (k x) , wp pt Q (Sigma.snd (k x))) i
wp {m = m} {{M}} pt Q (Spec {a'} pre post k) i = Pair (pre i) ((o : m a') → post i o → wp pt Q k o)

-- A consistent set of axiomatic and operational semantics for a Mix.
record Semantics (C : Set) (R : C → Set) (m : Set → Set) {{M : IsMonad m}} : Set where
  constructor semantics
  field
    pt : {a : Set} → (a → Sigma C λ c → Pre m (R c)) → Pre m a
    handler : (c : C) → m (R c) -- The variable part of the runner.

    pt-if : {a : Set} (c : a → C) {P P' : (x : a) → Pre m (R (c x))} →
      (∀ x o → P x o → P' x o) → ∀ o → pt (λ x → c x , P x) o → pt (λ x → c x , P' x) o
    lifter-bind : {a b : Set} (P : m b → Set) (k : a → Sigma C λ c → R c → m b)
      (i : m a) → pt (λ x → Sigma.fst (k x) , λ mr → P (mr >>= Sigma.snd (k x))) i ⇔ P (i >>= λ x → handler (Sigma.fst (k x)) >>= (Sigma.snd (k x)))
open Semantics

pt-iff : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  {a : Set} (c : a → C) (P P' : (x : a) → Pre m (R (c x))) →
  (∀ x o → P x o ⇔ P' x o) →
  ∀ o → pt s (λ x → c x , P x) o ⇔ pt s (λ x → c x , P' x) o
pt-iff s c P P' x o = iff
  (λ x₁ → pt-if s c (λ x₂ o₁ → _⇔_.if (x x₂ o₁)) o x₁)
  (λ x₁ → pt-if s c (λ x₂ o₁ → _⇔_.onlyIf (x x₂ o₁)) o x₁)

transformer : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  {a b : Set} → Post m a b → Mix C R m a b → Pre m a
transformer s Q p i = wp (pt s) (Q i) p i

runner : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  {a b : Set} → (p : Mix C R m a b) → isCode p → a → m b
runner s = run (handler s)

consistent : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  (s : Semantics C R m) →
  {a b : Set} → (P : Post m a b) →
  (p : Mix C R m a b) → (c : isCode p) →
  (i : m a) → transformer s P p i ⇔ P i (i >>= run (handler s) p c)
consistent s P (Pure x) tt i = ⇔-refl
consistent s P (Step k) ic i = ⇔-trans
  (pt-iff s (λ x → Sigma.fst (k x)) _ (λ x o → P i (o >>= run (handler s) (Sigma.snd (k x)) (ic x))) (λ x o → consistent s (\_ → P i) (Sigma.snd (k x)) (ic x) o) i)
  (lifter-bind s (P i) (λ x → Sigma.fst (k x) , run (handler s) (Sigma.snd (k x)) (ic x)) i)
consistent s P (Spec pre post k) () i

record Refine {a b : Set} {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}}
  (s : Semantics C R m) (p q : Mix C R m a b) : Set where
  constructor refine
  field
    proof : ∀ (i : m a) (P : Post m a b) → transformer s P p i → transformer s P q i

pre-Refine : ∀ {a b C R m} {{M : IsMonad m}} (s : Semantics C R m {{M}}) → Preorder (Refine {a} {b} {C} {R} {m} {{M}} s)
pre-Refine {a} {b} {C} {R} {m} s = Preorder.preorder (refine λ i P x → x) trans'
  where
  trans' : {x y z : Mix C R m a b} → Refine s x y → Refine s y z → Refine s x z
  trans' (refine xy) (refine yz) = refine λ i P x → yz i P (xy i P x)

record Impl {a b : Set} {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}}
  (s : Semantics C R m) (p : Mix C R m a b) : Set where
  constructor impl
  field
    prog : Mix C R m a b
    code : isCode prog
    refines : Refine s p prog

refine-itself : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} →
  (s : Semantics C R m) →
  (p : Mix C R m a b) (c : isCode p) →
  (P : Pre m a) (Q : Post m a b) →
  ((i : m a) → P i → Q i (i >>= run (handler s) p c)) →
  ({a : Set} (mx : m a) → fmap id mx == mx) →
  Refine s (spec P Q) p
refine-itself s@(semantics pt handler pt-if lifter-bind) p c P Q pf fmap-id = refine λ i R x → _⇔_.if (consistent s R p c i) (let mx = i >>= run handler p c in coerce (cong (R i) (fmap-id _)) (Pair.snd x (i >>= run handler p c) (pf i (Pair.fst x))))

isCodeBind : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b c : Set} →
  (mf : Mix C R m a b) (mg : Mix C R m b c) →
  (cf : isCode mf) (cg : isCode mg) →
  isCode (mf >=> mg)
isCodeBind (Pure f) (Pure g) tt tt = tt
isCodeBind (Pure f) (Step k) tt cg x = cg (f x)
isCodeBind (Pure f) (Spec pre post mg) tt ()
isCodeBind (Step k) mg cf cg x = isCodeBind (Sigma.snd (k x)) mg (cf x) cg
isCodeBind (Spec pre post mf) mg ()

doReturn : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  {a b : Set} →
  {s : Semantics C R m} → {P : Post m a b} →
  (f : a → b) →
  ({a : Set} (mx : m a) → fmap id mx == mx) →
  Impl s (spec (λ mx → P mx (fmap f mx)) P)
doReturn {C} {R} {m} {{M}} {a} {b} {s} {P} f fmap-id = impl (Pure f) tt (refine refines)
  where
  refines : ∀ (i : m a) (P' : Post m a b) →
    transformer s P' (spec (λ mx → P mx (fmap f mx)) P) i →
    transformer s P' (Pure f) i
  refines i P' (fst , snd) = coerce (cong (P' i) (fmap-id (fmap f i))) (snd (fmap f i) fst)

doSharpen : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} →
  {s : Semantics C R m} →
  {P P' : Pre m a} {Q Q' : Post m a b} →
  ((i : m a) → P' i → P i) → ((i : m a) (o : m b) → P' i → Q i o → Q' i o) →
  Impl s (spec P Q) → Impl s (spec P' Q')
doSharpen {C} {R} {m} {{M}} {a} {b} {s} {P} {P'} {Q} {Q'} pre post (impl prog code (refine proof)) =
  impl prog code (refine refines)
  where
  refines : (i : m a)
    (R : m a → m b → Set) →
    transformer s R (spec P' Q') i →
    transformer s R prog i
  refines i R (fst , snd) = proof i R (pre i fst , λ o z → snd o (post i o fst z))

wp-bind-Pure : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} →
  {s : Semantics C R m} →
  ({a b c : Set} → (f : a → b) (g : b → c) (mx : m a) → fmap g (fmap f mx) == fmap (g ∘ f) mx) →
  ({a b : Set} → (f : a → b) (c : b → C) (k : (x : b) → Pre m (R (c x))) (i : m a) →
    pt s (λ x → c x , k x) (fmap f i) ⇔ pt s (λ x → c (f x) , k (f x)) i) →
  {a b c : Set} →
  {P : m c → Set} →
  (f : a → b) (p : Mix C R m b c) (i : m a) →
  wp (pt s) P p (fmap f i) ⇔ wp (pt s) P (Pure f >=> p) i
wp-bind-Pure fmap-∘ pt-∘ {P = P} f (Pure g) i = ⇔-= {Q = P} (fmap-∘ f g i)
wp-bind-Pure {s = s} fmap-∘ pt-∘ {P = P} f (Step k) i =  pt-∘ f (λ x → Sigma.fst (k x)) (λ x x₁ → wp (pt s) P (Sigma.snd (k x)) x₁) i
wp-bind-Pure fmap-∘ pt-∘ f (Spec pre post p) i = ⇔-pair ⇔-refl ⇔-refl

doBind : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b c : Set} →
  {s : Semantics C R m} →
  {P1 : m a → Set} {P2 : m b → Set} {P3 : m c → Set} →
  ({a : Set} (mx : m a) → fmap id mx == mx) →
  ({a b c : Set} (f : a → b) (g : b → c) (mx : m a) → fmap g (fmap f mx) == fmap (g ∘ f) mx) →
  ({a b : Set} → (f : a → b) (c : b → C) (k : (x : b) → Pre m (R (c x))) (i : m a) →
    pt s (λ x → c x , k x) (fmap f i) ⇔ pt s (λ x → c (f x) , k (f x)) i) →
  Impl s (spec P1 (λ _ → P2)) → Impl s (spec P2 (λ _ → P3)) →
  Impl s (spec P1 (λ _ → P3))
doBind {C} {R} {m} {{M}} {a} {b} {c} {s} {P1} {P2} fmap-id fmap-∘ wp-∘ (impl prog code (refine proof)) (impl prog' code' (refine proof')) = impl
  (prog >=> prog')
  (isCodeBind prog prog' code code')
  (refine λ i P x → ref i prog prog' (proof i (λ _ → P2) (Pair.fst x , λ o x₁ → coerce (cong P2 (sym (fmap-id o))) x₁)) λ o x₁ → proof' o (λ _ → P i) (x₁ , λ o₁ x₂ → coerce (cong (P i) (sym (fmap-id o₁))) (coerce (cong (P i) (fmap-id o₁)) (Pair.snd x o₁ x₂))))
  where
  ref : {a b c : Set} {P2' : m b → Set} {P3' : m c → Set} (i : m a) (p : Mix C R m a b) (p' : Mix C R m b c) →
    wp (pt s) P2' p i →
    ((o : m b) → P2' o → wp (pt s) P3' p' o) →
    wp (pt s) P3' (p >=> p') i
  ref {P3'} i (Pure f) p' x x₁ = _⇔_.onlyIf (wp-bind-Pure {s = s} fmap-∘ wp-∘ f p' i) (x₁ (fmap f i) x)
  ref i (Step k) p' x x₁ = pt-if s (λ x₂ → Sigma.fst (k x₂)) (λ x₂ o x₃ → ref o (Sigma.snd (k x₂)) p' x₃ x₁) i x
  ref i (Spec pre post p) p' (fst , snd) x₁ = fst , λ o x → ref o p p' (snd o x) x₁

doReturn' : {C : Set} {R : C → Set} {m : Set → Set} {{M : IsMonad m}} {a b : Set} →
  {s : Semantics C R m} →
  ({a : Set} (mx : m a) → fmap id mx == mx) →
  {P : Pre m a} {Q : Post m a b} →
  (f : a → b) → (∀ i → P i → Q i (fmap f i)) →
  Impl s (spec P Q)
doReturn' {C} {R} {m} {{M}} {a} {s} fmap-id {P} f pf = impl
  (Pure f)
  tt
  (refine λ i P₁ x₁ → coerce (cong (P₁ i) (fmap-id (fmap f i))) (Pair.snd x₁ (fmap f i) (pf i (Pair.fst x₁))))
