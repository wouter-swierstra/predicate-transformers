{-#  OPTIONS --type-in-type #-}
module RelabelTest where

open import Prelude
open import Level

S : Set
S = Nat

K : Set -> S -> Set
K a _ = a

_⊆_ : {a : Set} ->
  (R1 R2 : a -> Set) -> Set
_⊆_ {a = a} R1 R2 =
  (x : a) -> R1 x -> R2 x 

-- Specifications as pre-posts conditions
record PT (A : Set) : Set where
  constructor [_,_]
  field
    pre : S -> Set
    post : Sigma S pre -> A × S -> Set

-- Semantics of specifications as predicate transformers
⟦_⟧ : ∀ {A} -> PT A -> (A × S -> Set) -> S -> Set
⟦ [ P , Q ] ⟧ R s = Sigma (P s) (\pres -> Q (s , pres) ⊆ R)


-- The state free monad -- extended with specs
data State (a : Set) : Set where
  Pure : a -> State a
  Get : (S -> State a) -> State a
  Put : S -> State a -> State a
  Spec : ∀ {b : Set} -> PT b -> (b -> State a) -> State a

fmap : ∀ {a b} -> (a -> b) -> State a -> State b
fmap f (Pure x) = Pure (f x)
fmap f (Get x) = Get \i -> fmap f (x i)
fmap f (Put x s) = Put x (fmap f s)
fmap f (Spec pt c) = Spec pt (\y -> fmap f (c y))

_>>=_ : ∀ {a b} -> State a -> (a -> State b) -> State b
Pure x >>= f = f x
Get x >>= f = Get (\i -> x i >>= f)
Put x c >>= f = Put x (c >>= f)
Spec pt c >>= f = Spec pt (\b -> c b >>= f)

_>>_ : ∀ {a b} -> State a -> State b -> State b
c1 >> c2 = c1 >>= (\_ -> c2)

put : S -> State ⊤
put s = Put s (Pure tt)

get : State S
get = Get Pure

spec : ∀ {a} -> PT a -> State a
spec pt = Spec pt Pure

return : ∀ {a} -> a -> State a
return = Pure

-- WP semantics of our State Free monad
wp : ∀ {A} -> State A -> (A × S -> Set) -> S -> Set
wp (Pure x) Q i = Q (x , i)
wp (Get x) Q i = wp (x i) Q i
wp (Put x c) Q i = wp c Q x
wp (Spec {b} pt c) Q s =
  -- relational composition?
  ⟦ pt ⟧ (\bs -> (wp (c (Pair.fst bs)) Q (Pair.snd bs))) s

_⊑_ : ∀ {A} -> State A -> State A -> Set
_⊑_ {A} s1 s2 = (R : A × S -> Set) -> wp s1 R ⊆ wp s2 R

-- Example derivation
freshSpec : PT S
freshSpec = [ K ⊤ , (\{ (x , _) (y , z) → (Succ x == z) × (y == x)}) ]

fresh : State S
fresh = get >>= \s ->
        put (Succ s) >>
        return s

correctness : spec freshSpec ⊑ fresh
correctness R x (tt , snd) = snd _ (Refl , Refl)


-- Auxiliary lemmas


-- GET
getPT : {a : Set} -> (s : S) -> PT a -> PT a
getPT s [ pre , post ] = [ (\i -> Pair (i == s) (pre i) )
                         , (\ { (fst , (eq , h)) xy → post (fst , h) xy }) ]
-- GET sound
getStepRefines : ∀ {a : Set} {spc : PT a} {c : S -> State a} ->
  ((s : S) -> spec (getPT s spc) ⊑ c s)->
  spec spc ⊑ Get c
getStepRefines {a} {spc} {c} H R x (y , z) = H x R x ((Refl , y) , z)

-- GET complete
getPT-complete : {a : Set} (s : S) (spc : PT a) {c : S -> State a} ->
  ((s : S) -> c s ⊑  spec (getPT s spc))->
  Get c ⊑ spec spc
getPT-complete s spc h1 R s' h2 =
  let (ih1 , ih2) = h1 s' R s' h2 in 
  Pair.snd ih1 , λ x x₁ → ih2 x x₁

getStep : ∀ {a : Set} {spc : PT a} ->
          ((s : S) -> Sigma (State a) (\c -> spec (getPT s spc) ⊑ c)) ->
          Sigma (State a) (\c -> spec spc ⊑ c)
getStep {a} {spc} f =
  (Get \s -> Sigma.fst (f s))
  , (getStepRefines {a} {spc} {\s -> Sigma.fst (f s)} \s -> Sigma.snd (f s))


-- PUT

putPT : ∀ {a} -> (z : S) -> PT a -> PT a
putPT z [ pre , post ] =
  [ (\s -> Pair (s == z) (pre z) ) , (λ { (s , x) y → (post (s , {!!}) y) })]

putStepRefines : ∀ {a : Set} {spc : PT a} {x : S} {c : State a} ->
            spec (putPT x spc) ⊑ c
        ->  spec spc ⊑ Put x c
putStepRefines {a} {spc} {x} {c} r R i (fst , snd) =
  r R x ((Refl , {!!}) , {!!})
--  r R x (((i , fst) , Refl) , λ {xy h → snd xy h})

putStep : ∀ {a : Set} {s : PT a} ->
            (x : S) ->
            Sigma (State a) (\c -> spec (putPT x s) ⊑ c) ->
            Sigma (State a) (\c -> spec s ⊑ c)
putStep {a} {s} x (c , R) = {!!}
-- Put x c , putStepRefines {a} {s} {x} {c} R

putPT-complete : {a : Set} {spc : PT a} {c : State a} (x : S) ->
  c ⊑ spec (putPT x spc) ->
  Put x c ⊑ spec spc
putPT-complete x h1 R y h2 with h1 R x h2
putPT-complete x h1 R y h2 | IH = {!!} 
--  {!!} , \xy h -> snd xy {!!}
--  let (((z , eq) , ih1b) , ih2) = h1 R x h2 in
--  {!ih1!} , λ xy p → ih2 xy {!p!}  

-- RETURN

returnStep : ∀ {a} {spc : PT a} -> (x : a) ->
  ((s : S) -> (pres : PT.pre spc s) -> PT.post spc ((s , pres)) (x , s)) ->
  Sigma (State a) (\c -> spec spc ⊑ c)
returnStep {a} {spc} x h = (Pure x) , λ { R s (fst , snd) → snd (x , s) (h s fst) }

-- How to formulate refinement problems
-- freshDerivation : Sigma (State S) (\c -> spec freshSpec ⊑ c)
-- freshDerivation =
--   getStep (\s ->
--   putStep (Succ s)
--   (returnStep s \{ i (( z , (eq , _)) , snd) → trans (cong Succ eq) (sym snd) , sym eq}))

