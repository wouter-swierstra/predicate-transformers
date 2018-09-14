module Relabel where

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
record PT (A : Set) : Set₁ where
  constructor [_,_]
  field
    pre : S -> Set
    post : Sigma S pre -> A × S -> Set

-- Semantics of specifications as predicate transformers
⟦_⟧ : ∀ {A} -> PT A -> (A × S -> Set) -> S -> Set
⟦ [ P , Q ] ⟧ R s = Sigma (P s) (\pres -> Q (s , pres) ⊆ R)

-- The state free monad -- extended with specs
data State (a : Set) : Set₁ where
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

consequence-wp :
  ∀ {A B} -> {P : B × S -> Set} (c : State A) (f : A -> State B) ->
  wp c (\{ (x , s') -> wp (f x) P s'}) ⊆ wp (c >>= f) P
consequence-wp (Pure x) f s H = H
consequence-wp (Get k) f s H = consequence-wp (k s) f s H
consequence-wp (Put x k) f s H = consequence-wp k f x H
consequence-wp (Spec spec k) f s (fst , snd) =
  fst , λ { (y , s') post → consequence-wp (k y) f s' (snd (y , s') post)}

-- Refinement
_⊑_ : ∀ {A} -> State A -> State A -> Set₁
_⊑_ {A} s1 s2 = (R : A × S -> Set) -> wp s1 R ⊆ wp s2 R

⊑-refl : ∀ {a} {c1 : State a} -> c1 ⊑ c1
⊑-refl = λ R s h → h

⊑-trans : ∀ {a} {c1 c2 c3 : State a} -> c1 ⊑ c2 -> c2 ⊑ c3 -> c1 ⊑ c3
⊑-trans p1 p2 R s h = p2 R s (p1 R s h)

_≈_ : ∀ {a} -> State a -> State a -> Set₁
c ≈ d = (c ⊑ d) × (d ⊑ c) 

-- Example derivation
freshSpec : PT S
freshSpec = [ K ⊤ , (\{ (x , _) (y , z) → (Succ x == z) × (x == y)}) ]

fresh : State S
fresh = get >>= \s ->
        put (Succ s) >>
        return s

correctness : spec freshSpec ⊑ fresh
correctness R x (tt , snd) = snd _ (Refl , Refl)

---
implements : ∀ {a} -> PT a -> State a -> Set₁
implements s c = spec s ⊑ c

derivation : ∀ {a} -> PT a -> Set₁
derivation {a} spec = Sigma (State a) (implements spec)

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
getPT-complete : {a : Set} (spc : PT a) {c : S -> State a} ->
  ((s : S) -> c s ⊑ spec (getPT s spc))->
  Get c ⊑ spec spc
getPT-complete spc h1 R s' h2 =
  let (ih1 , ih2) = h1 s' R s' h2 in 
  Pair.snd ih1 , λ x x₁ → ih2 x x₁

getStep : ∀ {a : Set} {spc : PT a} ->
          ((s : S) -> derivation (getPT s spc)) ->
          derivation spc
getStep {a} {spc} f =
  (Get \s -> Sigma.fst (f s))
  , (getStepRefines {a} {spc} {\s -> Sigma.fst (f s)} \s -> Sigma.snd (f s))

getCompleteness : {a : Set} (spc : PT a) {c : S -> State a} ->
  ((s : S) -> c s ≈ spec (getPT s spc)) ->
  Get c ≈ spec spc
getCompleteness {a} spc {c} H =
  getPT-complete {a} spc {c} (\s -> Pair.fst (H s))
  , getStepRefines {a} {spc} {c} (\s -> Pair.snd (H s))

-- PUT

putPT : ∀ {a} -> (z : S) -> PT a -> PT a
putPT z [ pre , post ] =
  [ (\s -> Pair (Sigma S pre) (z == s)) , (λ { (s , x) y → (post (Pair.fst x) y) })]

putStepRefines : ∀ {a : Set} {spc : PT a} {x : S} {c : State a} ->
            spec (putPT x spc) ⊑ c
        ->  spec spc ⊑ Put x c
putStepRefines {a} {spc} {x} {c} r R i (fst , snd) =
  r R x (((i , fst) , Refl) , λ {xy h → snd xy h})

-- This does not hold in general...
postulate
 putPT-complete : {a : Set} (spc : PT a) (c : State a) (x : S) ->
   c ⊑ spec (putPT x spc) ->
   Put x c ⊑ spec spc
-- putPT-complete spc c x H R i wpx with H R x wpx
-- ... | (((j , prej) , eq) , ihPost) = {!!} , \xy h -> ihPost xy {!!}

putCompleteness : {a : Set} (spc : PT a) (c : State a) (x : S) ->
  (c ≈ spec (putPT x spc)) ->
  Put x c ≈ spec spc
putCompleteness {a} spc c x (H1 , H2) =
  (putPT-complete spc c x H1 , putStepRefines {a} {spc} {x} {c} H2)


putStep : ∀ {a : Set} {s : PT a} ->
            (x : S) ->
            derivation (putPT x s) ->
            derivation s
putStep {a} {s} x (c , R) = Put x c , putStepRefines {a} {s} {x} {c} R


-- RETURN
returnStep : ∀ {a} {spc : PT a} -> (x : a) ->
  ((s : S) -> (pres : PT.pre spc s) -> PT.post spc ((s , pres)) (x , s)) ->
  derivation spc
returnStep {a} {spc} x h = (Pure x) , λ { R s (fst , snd) → snd (x , s) (h s fst) }

-- How to formulate refinement problems
freshDerivation : derivation freshSpec
freshDerivation =
  getStep (\s ->
  putStep (Succ s)
  (returnStep s \{ i (( z , (eq , _)) , snd) → trans (cong Succ eq) snd , eq}))


-- Tree relabelling

data Tree (a : Set) : Set where
  Leaf : a -> Tree a
  Node : (l r : Tree a) -> Tree a

flatten : ∀ {a} -> Tree a -> List a
flatten (Leaf x) = Cons x Nil
flatten (Node l r) = flatten l ++ flatten r

size : ∀ {a} -> Tree a -> Nat
size (Leaf x) = Succ Zero
size (Node l r) = size l + size r

seq : Nat -> Nat -> List Nat
seq i Zero = Nil
seq i (Succ n) = Cons i (seq (Succ i) n)

seqSplit : (y x z : Nat) -> seq x (y + z) == (seq x y ++ seq (x + y) z)
seqSplit Zero x z = cong (\x -> seq x z) (plus-zero _)
seqSplit (Succ y) x z = 
      Cons x (seq (Succ x) (y + z))
        ⟨ cong (Cons x) (seqSplit y (Succ x) z) ⟩
      Cons x (seq (Succ x) y ++ seq (Succ (x + y)) z)      
        ⟨ cong (\n -> Cons x (seq (Succ x) y ++ seq n z)) (plus-succ x y) ⟩
      Cons x (seq (Succ x) y ++ seq (x + Succ y) z)
      ■


relabelSpec : ∀ {a} -> (t : Tree a) -> PT (Tree Nat)
relabelSpec t = [ (K ⊤) ,
  (\ { (i , _) (t' , f) -> (f == (i + size t)) × (seq i (size t) == flatten t')}) ]

succ-lemma : (x : Nat) -> Succ x == (x + 1)
succ-lemma Zero = Refl
succ-lemma (Succ x) = cong Succ (succ-lemma x)


consequence' : ∀ {a b : Set} -> {pt1 : PT a}  {pt3 : PT b} ->
  (c1 : derivation pt1) ->
  (step : {s s' : S} {p : PT.pre pt1 s} {x : a} ->
           PT.post pt1 (s , p) (x , s') -> PT.pre pt3 s') ->
  (f : (x : a) ->
         derivation [ (\s' -> Sigma S
                              (\ i -> Sigma (PT.pre pt1 i)
                                            (\prei -> PT.post pt1 (i , prei) (x , s'))))
                      , (λ { (s , (s' , (pres1 , pres2))) (b , s'') →
                                PT.post pt3 (s , step pres2) (b , s'')})
--                    , (\ { (s' , (h1 , h2)) ys -> PT.post pt3 ( s' , h1) ys })
                    ]) ->
  derivation pt3 
consequence' (c1 , p) stp f = (c1 >>= \x -> Sigma.fst (f x))
  , \R s h -> consequence-wp c1 (\x -> Sigma.fst (f x)) s
     {!!}



consequence : ∀ {a b : Set} -> {pt1 : PT a} (pt2 : a -> PT b) {pt3 : PT b} ->
  (c1 : derivation pt1) -> 
  (f : (x : a) -> derivation (pt2 x)) ->
  (∀ {R s} -> ⟦ pt3 ⟧ R s ->  wp (Sigma.fst c1) (λ { (x , s') -> wp (Sigma.fst (f x)) R s' }) s) ->  
  derivation pt3 
consequence {pt1} pt2 {pt3} (c1 , p1) f H =
  (  (c1 >>= \x -> Sigma.fst (f x))
    , \R s A -> consequence-wp c1 (\x -> Sigma.fst (f x)) s (H A))


relabelDerivation : ∀ {a} -> (t : Tree a) ->
  Sigma (State (Tree Nat)) (implements (relabelSpec t))
relabelDerivation (Leaf x) =
  getStep \s ->
  putStep (Succ s)
  (returnStep (Leaf s) (proof s))
    where
      proof : (s t : Nat) ->
        (pres : (Sigma S (\z -> Pair (z == s) ⊤)) × (Succ s == t)) ->
        let ((u , _) , _) = pres in
        (t == (u + 1)) × (Cons u Nil == Cons s Nil)
      proof s .(Succ s) ((.s , (Refl , _)) , Refl) = (succ-lemma s , Refl)

relabelDerivation (Node l r) =
    consequence (\l' -> relabelSpec r) (relabelDerivation l)
    (\l' -> consequence (\r' -> relabelSpec (Node l r)) (relabelDerivation r)
    ((\r' -> returnStep (Node l' r') λ s pres → {!!} , {!!}))
    λ x → {!!})
    λ x → {!!}



         --   (seq s (size l + size r)
         --     ⟨ seqSplit (size l) s (size r) ⟩
         --   (seq s (size l) ++ seq (s + size l) (size r))
         --     ⟨ {!cong (\x -> seq s (size l) ++ seq (s + size l) (size r)) ? !} ⟩
         --   (flatten l' ++ flatten r')
         --   ■ ) }

      
