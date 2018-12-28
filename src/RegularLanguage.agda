{-# OPTIONS --type-in-type #-}
module RegularLanguage where

open import Prelude
open import Combined hiding (_++_)
open import Maybe

open import Data.Char hiding (_==_)
--open import Data.String
String = List Char

module Nondet where
  -- The type of nondeterministic computation:
  -- at each step, we might give up, or choose between two alternatives.
  data CNondet : Set where
    Fail : CNondet
    Split : CNondet
  RNondet : CNondet -> Set
  RNondet (Fail) = ⊥
  RNondet (Split) = Bool
  ENondet : Effect
  ENondet = CNondet , RNondet
  PTNondet : PT ENondet
  PTNondet Fail wp = ⊥
  PTNondet Split wp = Pair (wp True) (wp False)
  ESNondet : EffectSpec
  ESNondet = es ENondet PTNondet
open Nondet

module Recursion (I : Set) (O : I → Set) where
  ERec : Effect
  ERec = I , O
  ESRec : PT ERec → EffectSpec
  ESRec pt = es ERec pt
open Recursion

-- The constructors from `Just do it!'
fail : ∀ {a n} {Es : Vec n Effect} → Free (ESpec :: ENondet :: Es) a
fail = Step (FS F0) Fail magic
_[]_ : ∀ {a n} {Es : Vec n Effect} → Free (ESpec :: ENondet :: Es) a → Free (ESpec :: ENondet :: Es) a → Free (ESpec :: ENondet :: Es) a
p [] q = Step (FS F0) Split \c -> if c then p else q

-- You can choose to do nondeterminism or recursion.
NondetRec : (I : Set) (O : I → Set) → Set
NondetRec I O = (i : I) → Free (ESpec :: ENondet :: ERec I O :: vNil) (O i)

-- Syntax of regular expressions.
data Regex : Set where
  Empty : Regex -- The empty language, which doesn't contain the empty string!
  Epsilon : Regex
  Singleton : (c : Char) → Regex
  _∪_ : (l r : Regex) → Regex
  _·_ : (l r : Regex) → Regex
  _* : Regex → Regex

-- Inductively define when a string is in the regular language given by an expression.
data _∈[_] : String → Regex → Set where
  inEpsilon : Nil ∈[ Epsilon ]
  inSingleton : ∀ c → (c :: Nil) ∈[ Singleton c ]
  inUnionL : ∀ xs l r → xs ∈[ l ] → xs ∈[ l ∪ r ]
  inUnionR : ∀ xs l r → xs ∈[ r ] → xs ∈[ l ∪ r ]
  inConcat : ∀ xs ys zs l r → xs == ys ++ zs → ys ∈[ l ] → zs ∈[ r ] → xs ∈[ l · r ]
  inStarNil : ∀ r → Nil ∈[ r * ]
  inStarCons : ∀ xs r → xs ∈[ r · (r *) ] → xs ∈[ r * ]

record SplitList {a : Set} (xs : List a) : Set where
  constructor splitList
  field
    lhs : List a
    rhs : List a
    cat : xs == lhs ++ rhs

-continuation : ∀ {a} {xs : List a} (x : a) → SplitList xs → SplitList (x :: xs)
-continuation x spl = splitList (x :: SplitList.lhs spl) (SplitList.rhs spl) (cong (Cons x) (SplitList.cat spl))
-- Split the list nondeterministically into two pieces.
split : ∀ {a n} {Es : Vec n Effect} → (xs : List a) → Free (ESpec :: ENondet :: Es) (SplitList xs)
split Nil = Pure (splitList Nil Nil refl)
split (x :: xs) =
  Pure (splitList Nil (x :: xs) refl)
  []
  (split xs >>= λ spl → Pure (-continuation x spl))

-match-continuation : ∀ xs l r → SplitList xs → Free (ESpec :: ENondet :: ERec (Pair String Regex) (uncurry _∈[_]) :: vNil) (xs ∈[ l · r ])
-match-continuation xs l r (splitList ys zs cat) =
  Step (FS (FS F0)) (ys , l) λ ys∈l →
  Step (FS (FS F0)) (zs , r) λ zs∈r →
  Pure (inConcat xs ys zs l r cat ys∈l zs∈r)

-- Try to prove that the string is in the language.
-- If this is not the case, the nondeterministic computation fails.
-- We recurse both on the regex and the string,
-- so we need them both in the recursive call.
match : NondetRec (Pair String Regex) (uncurry _∈[_])
match (xs , Empty) = fail

match (Nil , Epsilon) = Pure inEpsilon
match ((x :: xs) , Epsilon) = fail

match (Nil , Singleton _) = fail
match ((x :: Nil) , Singleton c) with c ≟ x
... | yes refl = Pure (inSingleton c)
... | no _ = fail
match ((_ :: _ :: _) , Singleton _) = fail

match (xs , (l ∪ r)) =
  Step (FS (FS F0)) (xs , l) (λ x → Pure (inUnionL xs l r x))
  []
  Step (FS (FS F0)) (xs , r) (λ x → Pure (inUnionR xs l r x))

match (xs , (l · r)) = split xs >>= -match-continuation xs l r

match (Nil , (r *)) = Pure (inStarNil r)
match (xs@(_ :: _) , (r *)) = Step (FS (FS F0)) (xs , (r · (r *))) λ x →
  Pure (inStarCons xs r x)

apply-split : ∀ {a} {xs : List a} →
  (P : (xs ys zs : List a) → Set) →
  SplitList xs → Set
apply-split {a} {xs} P spl = P xs (SplitList.lhs spl) (SplitList.rhs spl)

split-partially-correct : ∀ {a n} {Es : Vec n EffectSpec} →
  (P : (xs ys zs : List a) → Set) →
  ((xs ys zs : List a) → xs == ys ++ zs → P xs ys zs) →
  (xs ys zs : List a) → WP.wp (ESNondet :: Es) (split xs) (apply-split P)
split-partially-correct P x Nil ys zs = x Nil Nil Nil refl
split-partially-correct P x (x₁ :: xs) ys zs = (x (x₁ :: xs) Nil (x₁ :: xs) refl) , WP.wp-bind _ {!!} (apply-split P) (split xs) (apply-split P) (λ spl → Pure (-continuation x₁ spl)) (split-partially-correct P x xs zs zs) λ x₂ x₃ → x _ _ _ (cong (Cons x₁) (SplitList.cat x₂))

-- Specification for match: if xs ∈[ r ] , then match finds a proof.
pt-match : PT (ERec (Pair String Regex) (uncurry _∈[_]))
pt-match (xs , r) wp = ∀ (pf : xs ∈[ r ]) → wp pf

match-partially-correct : (xs : String) (r : Regex) → xs ∈[ r ] → WP.wp (ESNondet :: ESRec _ _ pt-match :: vNil) (match (xs , r)) (const ⊤)
match-partially-correct .Nil .Epsilon inEpsilon = tt

match-partially-correct .(c :: Nil) .(Singleton c) (inSingleton c) with c ≟ c
match-partially-correct .(c :: Nil) .(Singleton c) (inSingleton c) | yes refl = tt
match-partially-correct .(c :: Nil) .(Singleton c) (inSingleton c) | no ¬p = magic (¬p refl)

match-partially-correct xs .(l ∪ r) (inUnionL .xs l r pf) = (λ x → tt) , (λ x → tt)
match-partially-correct xs .(l ∪ r) (inUnionR .xs l r pf) = (λ x → tt) , (λ x → tt)

-- TODO: can this be made more readable?
match-partially-correct xs .(l · r) (inConcat .xs ys zs l r xs=ys++zs pf pf₁) = WP.wp-bind _ {!!} (λ x → (ys == SplitList.lhs x) → (zs == SplitList.rhs x) → apply-split (λ xs₁ ys₁ zs₁ → xs₁ ∈[ l · r ]) x) (split xs) (const ⊤) (λ x → -match-continuation xs l r x) (split-partially-correct (λ xs' ys' zs' → ys == ys' → zs == zs' → xs' ∈[ l · r ]) (λ xs₁ ys₁ zs₁ x x₁ x₂ → inConcat xs₁ ys₁ zs₁ l r x (coerce (cong (λ z → z ∈[ l ]) x₁) pf) (coerce (cong (λ z → z ∈[ r ]) x₂) pf₁)) xs ys zs) λ x x₁ pf₂ pf₃ → tt

match-partially-correct .Nil .(r *) (inStarNil r) = tt

match-partially-correct Nil .(r *) (inStarCons .Nil r pf) = tt
match-partially-correct (x :: xs) .(r *) (inStarCons .(x :: xs) r pf) = λ pf₁ → tt
