{-# OPTIONS --type-in-type #-}
module MaybeEval where

open import Prelude
open import Level hiding (lift)
open import Free hiding (_⊑_)
open import Spec

-- Define the Partial / Maybe monad.
data C : Set where
  Abort : C
R : C -> Set
R Abort = ⊥
Partial : Set -> Set
Partial = Free C R

-- Smart constructors.
just     : forall { a } ->  a -> Partial a
just     = Pure
abort  : forall { a } ->  Partial a
abort  = Step Abort (\ ())

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

-- When we run Partial, we get a Maybe.
liftJust : {a : Set} -> (a -> Set) -> (Maybe a -> Set)
liftJust P Nothing = ⊥
liftJust P (Just x) = P x
rtPartial : RunType
rtPartial = types Maybe Just liftJust

-- Lift a predicate on base values to monadic values.
mustPT : PTs C R
mustPT P _ (Pure x) = P _ x
mustPT P _ (Step Abort _) = ⊥

-- Example: small expression language.
data Expr : Set where
  Val : Nat -> Expr
  Div : Expr -> Expr -> Expr

isSucc : Nat -> Set
isSucc Zero = ⊥
isSucc (Succ n) = ⊤

{-
postulate
  totalDiv : Nat -> (m : Nat) -> {p : isSucc m} -> Nat

div : Nat -> Nat -> Partial Nat
div n Zero = abort
div n (Succ k) = just (totalDiv n (Succ k))

-- Denotational semantics for the expression language.
⟦_⟧ : Expr -> Partial Nat
⟦ Val x ⟧      =  return x
⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                  ⟦ e2 ⟧ >>= \ v2 ->
                  div v1 v2

-- Operational semantics for the expression language.
data _⇓_ : Expr -> Nat -> Set where
  Base : ∀ {x} -> Val x ⇓ x
  Step : ∀ {x y l r} -> l ⇓ x -> r ⇓ (Succ y) ->
          Div l r ⇓ totalDiv x (Succ y)

wpPartial : {a : Set} -> {b : a -> Set} ->
  ((x : a) -> b x -> Set) ->
  ((x : a) -> Partial (b x)) ->
  (a -> Set)
wpPartial P = wp (mustPT P)

SafeDiv : Expr -> Set
SafeDiv (Val x) = (Val x) ⇓ Zero -> ⊥
SafeDiv (Div e e₁) = Triple (e₁ ⇓ Zero -> ⊥) (SafeDiv e) (SafeDiv e₁)

correct : (e : Expr) -> SafeDiv e -> wpPartial (\_ -> e ⇓_) ⟦_⟧ e
correct (Val x) nz = Base
correct (Div l r) (nz1 , nz2 , nz3) with ⟦ l ⟧ | ⟦ r ⟧ | correct l nz2 | correct r nz3
correct (Div l r) (nz1 , nz2 , nz3) | Pure x | Pure Zero | p | q = magic (nz1 q)
correct (Div l r) (nz1 , nz2 , nz3) | Pure x | Pure (Succ y) | p | q = Step p q
correct (Div l r) (nz1 , nz2 , nz3) | Pure x | Step Abort x₁ | p | ()
correct (Div l r) (nz1 , nz2 , nz3) | Step Abort x | y | p | q = p

correctWP : (e : Expr) -> SafeDiv e -> wpPartial (λ x → _⇓_ e) ⟦_⟧ e
correctWP e nz = correct e nz

-- Completeness and soundness (with some lemmata)
dom : {a : Set} -> { b : a -> Set} -> ((x : a) -> Partial (b x)) -> (a -> Set)
dom = wpPartial (\ _ _ -> ⊤)
complete  : wpPartial  _⇓_ ⟦_⟧  ⊆   dom ⟦_⟧
sound     : dom ⟦_⟧              ⊆   wpPartial _⇓_ ⟦_⟧ 
sound (Val x) h = Base
sound (Div e1 e2) h with ⟦ e1 ⟧ | ⟦ e2 ⟧ | sound e1 | sound e2
sound (Div e1 e2) () | Pure v1 | Pure Zero | ih1 | ih2
sound (Div e1 e2) h | Pure v1 | Pure (Succ v2) | ih1 | ih2 = Step (ih1 tt) (ih2 tt)
sound (Div e1 e2) () | Pure x | Step Abort x₁ | ih1 | ih2
sound (Div e1 e2) () | Step Abort x | v2 | ih1 | ih2

inDom : {v : Nat} -> (e : Expr) -> ⟦ e ⟧ == Pure v -> dom ⟦_⟧ e
inDom (Val x) h = tt
inDom (Div e1 e2) h with ⟦ e1 ⟧ | ⟦ e2 ⟧
inDom (Div e1 e2) () | Pure v1 | Pure Zero
inDom (Div e1 e2) h | Pure v1 | Pure (Succ v2) = tt
inDom (Div e1 e2) () | Pure _ | Step Abort _
inDom (Div e1 e2) () | Step Abort _ | _

wpPartial1 : {e1 e2 : Expr} -> wpPartial _⇓_ ⟦_⟧ (Div e1 e2) -> wpPartial _⇓_ ⟦_⟧ e1
wpPartial1 {e1} {e2} h with inspect ⟦ e1 ⟧
wpPartial1 {e1} {e2} h | Pure x with-≡ eq = sound e1 (inDom e1 eq)
wpPartial1 {e1} {e2} h | Step Abort x with-≡ eq rewrite eq = magic h

wpPartial2 : {e1 e2 : Expr} -> wpPartial _⇓_ ⟦_⟧ (Div e1 e2) -> wpPartial _⇓_ ⟦_⟧ e2
wpPartial2 {e1} {e2} h with inspect ⟦ e1 ⟧ | inspect ⟦ e2 ⟧
wpPartial2 {e1} {e2} h | Pure v1 with-≡ eq1 | Pure v2 with-≡ eq2
  = sound e2 (inDom e2 eq2)
wpPartial2 {e1} {e2} h | Pure _ with-≡ eq1 | Step Abort _ with-≡ eq2
  rewrite eq1 | eq2 = magic h
wpPartial2 {e1} {e2} h | Step Abort x with-≡ eq | _ rewrite eq = magic h

complete (Val x) h = tt
complete (Div e1 e2) h
  with inspect ⟦ e1 ⟧ | inspect ⟦ e2 ⟧
    | complete e1 (wpPartial1 {e1} {e2} h)
    | complete e2 (wpPartial2 {e1} {e2} h)
complete (Div e1 e2) h | Pure v1 with-≡ eq1 | Pure Zero with-≡ eq2 | ih1 | ih2
  rewrite eq1 | eq2 = magic h
complete (Div e1 e2) h | Pure v1 with-≡ eq1 | Pure (Succ v2) with-≡ eq2 | ih1 | ih2
  rewrite eq1 | eq2 = tt 
complete (Div e1 e2) h | Pure _ with-≡ _ | Step Abort _ with-≡ eq | _ | ih2
  rewrite eq = magic ih2
complete (Div e1 e2) h | Step Abort _ with-≡ eq | _ | ih1 | _
  rewrite eq = magic ih1

-- Assign predicate transformer semantics to a relation
wpR : ∀ {a b : Set} -> (R : a -> b -> Set) -> (b -> Set) -> (a -> Set)
wpR {a} {b} R P x = R x ⊆ P

_⊑_ : {a b : Set} ->
  (PT1 PT2 : (b -> Set) -> (a -> Set)) -> Set₁
_⊑_ {a} {b} PT1 PT2 = (P : b -> Set) -> PT1 P ⊆ PT2 P

-- correct2 : wpR (_⇓_)  ⊑ wp ⟦_⟧ 
-- correct2 P (Val x) H = H x Base
-- correct2 P (Div l r) H with
--     inspect ⟦ l ⟧ | correct2 P l {!!}
--   | inspect ⟦ r ⟧ | correct2 P r {!!}
-- correct2 P (Div l r) H | Pure vl with-≡ eql | cl | Pure vr with-≡ eqr | cr rewrite eql | eqr
--   with inspect (div vl vr)
-- ... | Pure v with-≡ eq rewrite eq = H v {!!}
-- ... | Step Abort _ with-≡ eq rewrite eq = {!v!}  
-- correct2 P (Div l r) H | Pure x with-≡ eql | cl | Step Abort _ with-≡ eqr | cr rewrite eqr
--   = magic cr
-- correct2 P (Div l r) H | Step Abort x with-≡ eql | cl | vr with-≡ eqr | cr rewrite eql
--   = magic cl

correct2' : wpR (_⇓_)  ⊑  \P -> wpPartial (\_ -> P) ⟦_⟧ 
correct2' P (Val x) H = H x Base
correct2' P (Div l r) H with ⟦ l ⟧ | ⟦ r ⟧
... | sl | sr = {!how can we rule out that the division fails?!}

lemma : ∀ {P : Nat -> Set} {x y v1 v2} ->
  x == v1 -> Succ y == v2 -> mustPT (λ _ → P) y (div v1 v2) -> P (totalDiv x (Succ y))
lemma {P} {x} {y} {.x} {.(Succ y)} Refl Refl H = H

wpLemma : (e : Expr) (v : Nat) -> ⟦ e ⟧ == just v -> {!!} e
wpLemma e v H with ⟦ e ⟧
wpLemma e .x Refl | Pure x = Refl
wpLemma e v () | Step Abort x

correct3 : {!!} ⊑  wpR (_⇓_)
correct3 P (Val x) H .x Base = H
correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr) with inspect ⟦ l ⟧ | inspect ⟦ r ⟧
correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step {x} {y} evl evr)
  | Pure vl with-≡ eql | Pure vr with-≡ eqr rewrite eql | eqr =
  let ihl = correct3 (\n -> n == vl) l (wpLemma l vl eql) x evl
      ihr = correct3 (\n -> n == vr) r (wpLemma r vr eqr) _ evr
  in lemma ihl ihr H
correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr)
  | Pure x with-≡ eql | Step Abort x₁ with-≡ eqr rewrite eql | eqr = magic H
correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr)
  | Step Abort x with-≡ eql | Pure x₁ with-≡ eqr rewrite eql = magic H
correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr)
  | Step Abort x with-≡ eql | Step Abort x₁ with-≡ eqr rewrite eql = magic H




mustPTEq : (e : Expr) -> (v : Nat) -> ⟦ e ⟧ == Pure v ->  {!!}
mustPTEq e v eq rewrite eq = Refl

data Spec (a b : Set) : Set₁ where
  [_,_] : (pre : a -> Set) -> (post : (x : a) -> pre x -> b -> Set) -> Spec a b

refines : ∀ {a b} -> Spec a b -> Spec a b -> Set
refines {a} {b} [ pre1 , post1 ] [ pre2 , post2 ] =
  Sigma ((x : a) -> pre1 x -> pre2 x)
        (λ c → (x : a) (H : pre1 x) (y : b) -> post2 x (c x H) y -> post1 x H y)

wpsemantics : ∀ {a b} -> Spec a b -> (b -> Set) -> (a -> Set)
wpsemantics {a} {b} [ pre , post ] P = \x ->
  Sigma (pre x) \H -> (y : b) -> post x H y -> P y

refinementCorrect : ∀ {a b} -> (s1 s2 : Spec a b) ->
  refines s1 s2 -> (P : b -> Set) (x : a) -> wpsemantics s1 P x ->  wpsemantics s2 P x
refinementCorrect [ pre1 , post1 ] [ pre2 , post2 ] (preC , postC ) P x (pre , post) =
    (preC x pre) , λ y H → post y (postC x pre y H)


ruleOfConsequence : {a b : Set} (c : Partial a) (f : a -> Partial b) ->
  (P : b -> Set) -> {!!} -> {!!}
ruleOfConsequence (Pure x) f H P with f x
ruleOfConsequence (Pure x) f H P | Pure x₁ = P
ruleOfConsequence (Pure x) f H () | Step Abort x₁
ruleOfConsequence (Step Abort x) f H ()    

step : {a b : Set} {c : Partial a} {f : a -> Partial b} ->
  {P : b -> Set} -> {!!} -> {!!}
step {a} {b} {c} {f} {P} = ruleOfConsequence c f P

--  wp : {a b : Set} ->
--    (a -> Partial b) -> (b -> Set) -> (a -> Set)
--  wp f P x = mustPT P (f x)


correct4 : (e : Expr) -> SafeDiv e -> {!!}
correct4 (Val x) sd = Base
correct4 (Div l r) (fst , snd , thd) =
  step {c = ⟦ l ⟧}
  {!step {c = ⟦ r ⟧} ?!}

                  -- step {! ⟦ l ⟧ !} (\ v1 ->
                  -- ⟦ r ⟧ >>= \ v2 ->
                  -- div v1 v2 ) (\v -> Div l r ⇓ v) H



-}

-- Introduce specifications into the mix.
M : {a : Set} -> (a -> Set) -> Set
M = Mix C R rtPartial

PreM : (a : Set) -> Set
PreM = Pre rtPartial
PostM : (a : Set) -> (b : a -> Set) -> Set
PostM = Post rtPartial
liftM :  {a : Set} {b : a -> Set} -> (P : (x : a) -> b x -> Set) -> PostM a b
liftM = liftPost rtPartial

wpM : {a : Set} -> {b : a -> Set} ->
  (P : PostM a b) ->
  (f : (x : a) -> M b) ->
  (PreM a)
wpM {a} {b} = wpMix mustPT

record _⊑_ {a : Set} {b : a -> Set} (f g : (x : a) -> M b) : Set1 where
    constructor refinement
    field
      proof : ∀ P -> wpM (liftM P) f ⊆ wpM (liftM P) g

⊑-refl : ∀ {a} {b : a -> Set} -> (f : (x : a) -> M b) -> f ⊑ f
⊑-refl f = refinement \P x H -> H

⊑-trans : ∀ {a} {b : a -> Set} -> {f g h : (x : a) -> M b} -> f ⊑ g -> g ⊑ h -> f ⊑ h
⊑-trans (record { proof = step1 }) (record { proof = step2 }) =
  refinement \P H x -> step2 P H (step1 P H x)

strengthenPost : {a : Set} {b : a -> Set}
  -> (S1 S2 : PostM a b)
  -> (pre : PreM a)
  -> ((x : a) -> S2 x ⊆ S1 x)
  -> (\x -> specI pre S1) ⊑ \x -> specI pre S2
strengthenPost S1 S2 Pre H = refinement λ { P x (fst , snd) → fst , λ bx s2 → snd bx (H _ bx s2)}

-- Does running this monadic value work?
isCode' : {a : Set} {b : a -> Set} -> M b -> Set
isCode' (Pure (Done x)) = ⊤
isCode' (Pure (Spec pre post)) = ⊥
isCode' (Step Abort x) = ⊤

-- Does running this monadic computation work?
isCode : {a : Set} {b : a -> Set} -> (a -> M b) -> Set
isCode {a} prog = (x : a) -> isCode' (prog x)

run' : {a : Set} {b : a -> Set} {x : a} (prog : M b) -> isCode' prog -> Maybe (b x)
run' (Pure (Done x₁)) prf = Just x₁
run' (Pure (Spec pre post)) ()
run' (Step Abort k) prf = Nothing

run : {a : Set} {b : a -> Set}
  -> (prog : a -> M b) -> (isCode prog)
  -> (x : a) -> Maybe (b x)
run {a} {b} prog prf x = run' (prog x) (prf x)

wpPure : {a : Set} {b : a -> Set}
  -> (i : a) -> (y : b i)
  -> (P : b i -> Set)
  -> wpM (liftM \x -> P) (\x -> done y) i -> P y
wpPure i y P x = x

-- wpM P prog x is equivalent to wpM' P x (prog x)
wpM' : {a : Set} {b : a -> Set}
  -> (P : PostM a b)
  -> (x : a) -> (prog : M b) -> Set
wpM' P = mustPT (flip (wpI P))

accentize : {a : Set} {b : a -> Set}
  -> (P : PostM a b)
  -> (prog : a -> M b) -> (x : a)
  -> wpM P prog x -> wpM' P x (prog x)
accentize _ _ _ x₁ = x₁
unaccentize : {a : Set} {b : a -> Set}
  -> (P : PostM a b)
  -> (prog : a -> M b) -> (x : a)
  -> wpM' P x (prog x) -> wpM P prog x
unaccentize _ _ _ z = z

-- wpM always gives a valid precondtion
runSoundness : {a : Set} {b : a -> Set}
  -> (P : PostM a b)
  -> (prog : a -> M b) -> (prf : isCode prog)
  -> (x : a) -> wpM P prog x -> P x (run prog prf x)
runSoundness {a} {b} P prog prf x wpHolds = runSoundness' (prog x) (prf x) x (accentize P prog x wpHolds)
  where
  runSoundness' : (prog' : M b) -> (prf' : isCode' prog') -> (x : a) -> wpM' P x prog' -> P x (run' prog' prf')
  runSoundness' (Pure (Done output)) _ _ z = z
  runSoundness' (Pure (Spec pre post)) ()
  runSoundness' (Step Abort x) _ _ ()
-- wpM gives the weakest precondition, as long as the postcondition is false on Nothing
runCompleteness : {a : Set} {b : a -> Set}
  -> (pre : a -> Set) -> (post : (x : a) -> (b x) -> Set)
  -> (prog : a -> M b) -> (prf : isCode prog)
  -> ((x : a) -> pre x -> (liftM post) x (run prog prf x)) -- if the precondition causes the postcondition
  -> (pre ⊆ wpM (liftM post) prog) -- then the precondition implies the wp
runCompleteness {a} {b} pre post prog prf preCausesPost x preHolds
  = unaccentize (liftM post) prog x (runCompleteness' (prog x) (prf x) (preCausesPost x preHolds))
  where
  runCompleteness' : (prog' : M b) (prf' : isCode' prog')
    -> liftM post x (run' prog' prf')
    -> wpM' (liftM post) x prog'
  runCompleteness' (Pure (Done _₁)) prf' postHolds = postHolds
  runCompleteness' (Pure (Spec pre post)) ()
  runCompleteness' (Step Abort k) prf' postHolds = postHolds

{-
weakenPost : {a : Set} {b : a -> Set}
  -> (P post : (x : a) -> b x -> Set) -> ((x : a) -> (y : b x) -> post x y -> P x y)
  -> (prog : a -> M b)
  -> (x : a) -> wpM prog post x -> wpM prog P x
weakenPost P post postImpliesP prog x x₂ = {!!}
-}
-- If the postcondition is weaker, the precondition is as well.
weakenPost' : {a : Set} {b : a -> Set}
  -> (x : a)
  -> (P post : PostM a b)
  -> (post x ⊆ P x)
  -> (prog : a -> M b)
  -> wpM post prog x -> wpM P prog x
weakenPost' {a} {b} x P post x₁ prog wpPost = unaccentize P prog x (wp'' (prog x) (accentize post prog x wpPost))
  where
    wp'' : (prog' : M b) -> wpM' post x prog' -> wpM' P x prog'
    wp'' (Pure (Done x₂)) = x₁ (Just x₂)
    wp'' (Pure (Spec pre post)) = λ z → Pair.fst z , (λ x₂ x₃ → x₁ x₂ (Pair.snd z x₂ x₃))
    wp'' (Step Abort _) z = z

-- If wp P of a spec always holds, then its postcondition implies P.
wpSpec : {a : Set} {b : a -> Set} (pre : a -> Set)
  -> (post P : PostM a b)
  -> ((x : a) -> (wpM P (\_ -> specI pre post) x))
  -> ((i : a) -> post i ⊆ P i)
wpSpec pre post P wpHolds input output postHolds = Pair.snd (wpHolds input) output postHolds
wpSpec' : {a : Set} {b : a -> Set} (pre : a -> Set)
  -> (post P : PostM a b)
  -> (x : a) -> (wpM P (\_ -> specI pre post) x)
  -> (y : Maybe (b x)) -> post x y -> P x y
wpSpec' pre post P x x₁ y x₂ = Pair.snd x₁ y x₂

-- If the precondition of a spec holds, so does the wp of its postcondition.
wpSpecPost : {a : Set} {b : a -> Set} (pre : a -> Set)
  -> (post : PostM a b)
  -> (x : a) -> (pre x) -> (wpM post (\_ -> specI pre post) x)
wpSpecPost pre post x preX = preX , (λ x₁ z → z)

-- If running a program on a precondition guarantees the program terminates and satisfies a postcondition,
-- then the program refines the specification.
-- In other words: a program is its own reference implementation.
progRefinesItsSpec : {a : Set} {b : a -> Set}
  -> (pre : a -> Set) (post : (x : a) -> (b x) -> Set)
  -> (prog : a -> M b) -> (prf : isCode prog)
  -> ((x : a) -> pre x -> liftM post x (run prog prf x))
  -> (\_ -> specI pre (liftM post)) ⊑ prog
progRefinesItsSpec {a} {b} pre post prog prf x = refinement pris'
  where
  pris' : (P : (x : a) -> b x -> Set) -> (i : a) -> wpM (liftM P) (\_ -> specI pre (liftM post)) i -> wpM (liftM P) prog i
  pris' P i (fst , snd)
    = weakenPost' i (liftM P) (liftM post) snd prog
      (runCompleteness {b = b} pre post prog prf x i fst)

