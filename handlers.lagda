\documentclass[acmsmall, anonymous, review=false]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}

%include polycode.fmt
%include agda.fmt
%include handlers.fmt

%include preamble.tex

\begin{document}
\title{Algebraic effects: specification and refinement}

\author{Wouter Swierstra}

\affiliation{
\institution{Universiteit Utrecht}
}
\email{w.s.swierstra@@uu.nl}

\begin{abstract}
Insert abstract here.
\end{abstract}

%include ccs.tex

\maketitle

\section{Introduction}
\label{sec:intro}

Pure functional programs are good for reasoning. But real programs use
effects. Recently, algebraic effects have arisen as a way to embed
effectful operations in a purely functional language.

How can we reason about programs with algebraic effects? What is the
specification of a program written using algebraic effects?  How can
we show that a program satisfies a specification? Or indeed derive a
program from its specification?

This paper attempts to answer these questions by presenting a general
framework for deriving a verified effectful program from its
specification. The key techniques developed herein are:

\begin{itemize}
\item We show how the syntax of effects may be given by a free monad
  (arising from command-response pair or interaction structure). The
  semantics are given by a \emph{handler} -- or some form of
  interpretation of these effects. Typically, such handlers run the
  associated computation and produce some result. We show how we can
  also describe the behaviour of a program more abstractly by writing
  handlers that compute a \emph{proposition}. By proving a soundness
  result, we can relate this proposition is to a given handler. These
  propositional handlers show how to lift any predicate on the result
  of an effectful computation to a predicate on the entire
  computation.
\item Next we show how to assign \emph{predicate transformer
    semantics} to (Kleisli) arrows. Together with the propositional
  handlers, this gives us the machinery to specify the desired outcome
  of an effectful computation and assign it a weakest precondition
  semantics.
\item These weakest precondition semantics give rise to a notion of
  refinement on computations using algebraic effects. The resulting
  refinements that arise in this fashion are familiar for a wide range
  of example effects studied in this paper. This provides further
  evidence that the techniques presented here provide a unified
  framework for specifying and reasoning about impure computations.
\end{itemize}

The examples, theorems and proofs have all been formally verified in
the dependently typed programming language Agda\todo{citation}. The
sources associated withour our development are available\todo{here}.

% \item Where free monad describes the \emph{syntax} of operations,
%   their meaning is given by a separate interpretation or
%   \emph{handler}. To talk about the correctness of a program written
%   using free monads therefore must always be with respect to a certain
%   handler. To do so, we show how to compute propositional values that
%   are sound with respect to a given handler. Using such handlers, we
%   can define traditional \emph{predicate transformer semantics} for a
%   variety of algebraic effects.
  
% \item Using such predicate transformer semantics, we can define a
%   generic notion of \emph{program refinement}, allowing the
%   calculation of (effectful) programs from their specification. The
%   notion of refinement we end up with depends on the semantics
%   (handler) du jour:
%   \begin{itemize}
%   \item for pure functions, |f refines g| corresponds to extensional
%     equality between functions |f| and |g|;
%   \item for partial functions (Maybe), |f refines g| holds when |dom
%     (f) subset dom(g)| and |f| and |g| agreeing on |dom(f)|.
    
%   \item for nondeterministic computations and the |All| handler, |f
%     refines g| for all inputs |x|, |f x subset g x|. (hypothesis)
%   \item for nondeterministic computations and the |Any| handler, |f
%     refines g| for all inputs |x|, |f x subset g x|. (hypothesis)
%   \item for stateful computations, the refinement relation corresponds
%     closely to the traditional refinement relation on Dijkstra's
%     guarded command language.
    
%   \end{itemize}
% \end{itemize}

\section{Warm-up}
\label{sec:intro}
%if style == newcode
\begin{code}
module Check where

open import Prelude
open import Level hiding (lift)

module Free where
\end{code}
%endif

We begin by defining a data type for free monads in Agda in the style
of Hancock and Setzer:

\begin{code}
  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
\end{code}

You may want to think of |C| as being the type of \emph{commands}. A
computation described by the free monad |Free C R| either returns a
result of type |a| or issues a command |c : C|. For each |c : C|,
there is a set of responses |R c|. The second argument of the |Step|
constructor corresponds to the continuation, describing how to proceed
after receiving a response of type |R c|. It is straightforward to
show that the |Free| data type is indeed a monad:
\begin{code}
  fmap : (Forall (C R a b)) (a -> b) -> Free C R a -> Free C R b
  fmap f (Pure x) = Pure (f x)
  fmap f (Step c k) = Step c (\ r -> fmap f (k r)) 

  return : (Forall (C R a)) a -> Free C R a
  return = Pure
  _>>=_ : (Forall (C R a b)) Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x   >>= f  = f x
  Step c x >>= f  = Step c (\ r -> x r >>= f)
\end{code}
Finally, we will sometimes \emph{fold} over elements of |Free C R a|
using the following recursion principle:
\begin{code}
  fold : (Forall(C R a l)) (implicit(b : Set l)) ((c : C) -> (R c -> b) -> b) -> (a -> b) -> Free C R a -> b
  fold alg pure (Pure x) = pure x
  fold alg pure (Step c k) = alg c (\ r -> fold alg pure (k r))
\end{code}

\section{Maybe}
\label{sec:maybe}
%if style == newcode
\begin{code}
module Maybe where

  open Free
\end{code}
%endif

We can define the familiar |Maybe| monad by making the following
choice for |C| and |R|:
\begin{code}
  data C : Set where
    Nothing : C

  R : C -> Set
  R Nothing = ⊥

  Maybe : Set -> Set
  Maybe = Free C R
\end{code}
It is sometimes convenient to define the familiar constructors of the
|Maybe| type
\begin{code}
  just     : (Forall(a)) a -> Maybe a
  just     = Pure

  nothing  : (Forall(a)) Maybe a
  nothing  = Step Nothing (\ ())
\end{code}
A computation of type |Maybe a| will either return a value of type |a|
or fail (and return |nothing|).  One way to define a specification for
such computations, is by \emph{lifting} a predicate |P : a -> Set| to
computations of type |Maybe a|:
\begin{code}
  lift : (Forall(a)) (P : a -> Set) -> Maybe a -> Set
  lift P (Pure x)          = P x
  lift P (Step Nothing _)  = ⊥
\end{code}
Alternatively, we could
have defined |lift| using our |fold| function, mapping |Nothing| to
bottom:
\begin{spec}
  lift = fold (\ { Nothing x → ⊥ })
\end{spec}
For any predicate |P : a -> Set|, the statement |lift P| specifies
when a computation of type |Maybe a| will successfully return a value
of type |a| satisfying |P|.

\subsection*{Example: evaluation}
\label{sec:evaluation}

We can define a small expression language consisting of natural
numbers and division:

\begin{code}
  data Expr : Set where
    Val : N -> Expr
    Div : Expr -> Expr -> Expr
\end{code}

%if style == newcode
\begin{code}
  div : Nat -> Nat -> Maybe Nat
  div n Zero = nothing
  div n (Succ k) = return n
\end{code}
%endif

When evaluating these expressions, we may encounter division by zero
errors. Our evaluator therefore returns a value of |Maybe Nat|:
\begin{code}
  ⟦_⟧ : Expr -> Maybe Nat
  ⟦ Val x ⟧      =  return x
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    div v1 v2
\end{code}
Here we assume an auxiliary function |div : Nat -> Nat -> Maybe Nat|,
that can be used to compute the integer division of two natural
numbers.

How can we reason about our evaluator?  Or specify its intended
behaviour? Using our |lift| function, we can lift any predicate on
|Nat| to a predicate on expressions as follows:
\begin{code}
  wp : (Nat -> Set) -> (Expr -> Set)
  wp P = \ e -> lift P ⟦ e ⟧
\end{code}
As the name suggests, |wp| computes the \emph{weakest precondition} on
the input expression |e| that must hold to ensure that the result of
evaluating |e| satisfies |lift P|.

For example, we specify the domain of our semantics |⟦_⟧| by
instantiating |P| to be the trivial predicate:
\begin{code}
  dom : Expr -> Set
  dom = wp (\ _ -> top)
\end{code}

Using our |dom| predicate, it is easy to check that:

\begin{code}
  test1 : dom (Val 3) == top
  test2 : dom (Div (Val 1) (Val 0)) == ⊥
\end{code}

%if style == newcode
\begin{code}
  test1 = Refl
  test2 = Refl
\end{code}
%endif

\paragraph{Soundness}

Our |lift| function computes a predicate on computations of type
|Maybe a| -- how can we know that this predicate is well-behaved with
respect to the intended semantics of our monad?

Consider the usual `handler' for |Maybe| that returns a default
value when encountering a failure:

\begin{code}
  run : (Forall (a)) a -> Maybe a -> a
  run d (Pure x)          = x
  run d (Step Nothing _)  = d
\end{code}
To prove the soundness of our |lift| function with respect to this
handler amounts to proving:
\begin{spec}
  soundness : (Forall(a)) (d : a) (P : a -> Set) (m : Maybe a) -> lift P m -> P (run d m)
\end{spec}
The proof of this result follows trivially after pattern matching on
|m|.

\paragraph{Intermezzo: types, specifications, and predicate transformers}

Before studying other effects, it is worth making the construction of
specifications more explicit.
\begin{itemize}
\item A specification on a value of type |A| is a predicate |A ->
  Set|;
\item A specification of a function of type |A -> B| is a
  \emph{predicate transformer} of type |(B -> Set) -> (A -> Set)|.
\end{itemize}
You may recognise this construction as the contravariant Hom functor
on |Set|, i.e., |Hom(_,Set)|. In our example evaluator, we wanted to
specify the behaviour of a function of type |Expr -> Maybe Nat|. By
using the |lift| function, this amounts to a predicate transformer of
the form |(Nat -> Set) -> (Expr -> Set)|.

This pattern can be extended to many other effects, as we shall
explore now.

\section{State}
\label{sec:state}

We can do something similar for mutable state. We will define a module
parametrized by a type |s|, representing the type of our mutable
state:

\begin{code}
module State (s : Set) where
\end{code}

%if style == newcode
\begin{code}
  open Free  
\end{code}
%endif

As before, we assemble our free monad from the commands |C| and
responses |R|:

\begin{code}
  data C : Set where
    Get : C
    Put : s -> C

  R : C -> Set
  R Get      = s
  R (Put _)  = ⊤

  State : Set -> Set
  State = Free C R
\end{code}

Once again, we can define a pair of smart constructors to make it
easier to write stateful computations:
\begin{code}
  get : State s
  get = Step Get return

  put : s -> State ⊤
  put s = Step (Put s) (\_ -> return tt)
\end{code}

The usual handler for stateful computations maps our free monad,
|State s|, to the state monad:
\begin{code}
  run : (Forall(a)) State a -> s -> Pair a s
  run (Pure x) s          = (x , s)
  run (Step Get k) s      = run (k s) s
  run (Step (Put x) k) s  = run (k tt) x 
\end{code}
Inspired by the previous sections, we can define the following
predicate transformer semantics:
\begin{code}
  lift : (Forall(a)) (P : Pair a s -> Set) -> State a -> (s -> Set)
  lift P (Pure x) s           = P (x , s)
  lift P (Step Get k) s       = lift P (k s) s
  lift P (Step (Put s') k) s  = lift P (k tt) s'
\end{code}
Given any predicate |P| on the final state and result, it
computes the weakest precondition required of the initial state to
ensure |P| holds upon completing the computation.

Once again, we can prove soundness of this predicate transformer with
respect to the |run| above:

\begin{code}
  soundness : (Forall(a)) (P : Pair a s -> Set) -> (c : State a) -> (i : s) -> lift P c i -> P (run c i)
\end{code}
%if style == newcode           
\begin{code}           
  soundness P (Pure x) i p = p
  soundness P (Step Get x) i lift = soundness P (x i) i lift
  soundness P (Step (Put x) k) i lift with soundness P (k tt)
  ... | ih = ih x lift             
\end{code}
%endif

We oftentimes want to write a specification as a \emph{relation}
between input and output states. To do so, we can partially apply the
predicate |P| before calling |lift|:
\begin{code}
  liftR : {a : Set} -> (P : s -> a -> s -> Set) -> State a -> (s -> Set)
  liftR P c s = lift (uncurry (P s)) c s
\end{code}
Reusing our previous soundness result, we can show that the |liftR|
is sound with respect to the |run| semantics defined above.

\subsection*{Example: tree labelling}
\label{sec:trees}

\todo{Do example}

\subsection*{Rule of consequence}
\label{sec:consequence}





\section{Nondeterminism}
\label{sec:non-det}

Can we repeat this construction of predicate transformer semantics for
other effects? In this section, we will show how we can lift a
predicate |a -> Set| over non-deterministic computations returning
values of type |a|. Once again, we begin by defining a free monad
describing the effects that can be used to describe non-deterministic
computations:

%if style == newcode
\begin{code}
module Nondeterminism where

  -- Define a free monad
  open Free
\end{code}
%endif

\begin{code}
  data C : Set where
    Fail : C
    Choice : C

  R : C -> Set
  R Fail = ⊥
  R Choice = Bool
\end{code}

Here we have chosen to define two possible commands: |Fail| and
|Choice|. The |Fail| constructor corresponds to a non-deterministic
computation that will not return any results; conceptually, the
|Choice| constructor takes two arguments and non-deterministically
chooses between them. To model this, the response used in the
continuation of the free monad, |R Choice|, is a |Bool|, indicating
which argument to choose. We can make this more clear by defining the
following shorthands for non-deterministic computations, |ND|, and
its constructors:
\begin{code}
  ND : Set -> Set
  ND = Free C R

  fail : (Forall(a)) ND a
  fail = Step Fail (\ ())

  choice : (Forall(a)) ND a -> ND a -> ND a
  choice c1 c2 = Step Choice (\ b -> if b then c1 else c2)
\end{code}

Next, we turn our attention to lifting a predicate of type |a -> Set|
to computations of type |ND a -> Set|. There are two canonical ways to
do so:

> All : (Forall(a)) (P : a -> Set) -> ND a -> Set
> All P (Pure x) = P x
> All P (Step Fail _) = ⊤
> All P (Step Choice c) = Pair (All P (c True)) (All P (c False)) 
> 
> Any : (Forall(a)) (P : a -> Set) -> ND a -> Set
> Any P (Pure x) = P x
> Any P (Step Fail _) = ⊥
> Any P (Step Choice c) = Either (Any P (c True)) (Any P (c False))

The statement |All P nd| holds when |P| holds for \emph{all} possible
values returned by the non-deterministic computation |nd|; the
statement |Any P nd| holds when |P| holds for \emph{any} possible
value returned by the non-deterministic computation |nd|. Both these
functions could also be defined using |fold|, for instance:

> All' :  (Forall(a)) (P : a -> Set) -> ND a -> Set
> All' = fold (\ { Fail _ → ⊤ ; Choice k → Pair (k True) (k False) })

We can relate both these predicates to the usual `list handler' for
non-determinism and prove appropriate soundness results.

\subsection*{Example}
\label{example-non-det}

Using these handlers, we can reason about non-deterministic
computations. The |guard| function, for example, can be used to prune
computations to satisfy a given predicate:

\begin{code}
  guard : (Forall(a))  (p : a -> Bool) -> a -> ND a
  guard p x = if p x then return x else fail
\end{code}
Subsequently, we can prove that guard will always return results
satisfying |P|:
\begin{code}
  guardCorrect : (Forall(a)) (p : a -> Bool) -> (x : a) -> All (\ x -> So (p x)) (guard p x)
\end{code}
%if style == newcode
\begin{code}
  guardCorrect p x with inspect (p x)
  guardCorrect p x | True with-≡ eq rewrite eq = lemma (p x) eq
    where
      lemma : (b : Bool) -> b == True -> So b
      lemma True p = tt
      lemma False ()
  guardCorrect p x | False with-≡ eq rewrite eq = tt
\end{code}
%endif

\todo{Bigger example? n-queens?}

\section{General recursion, totally free}

Besides these well-known effects, we can handle \emph{general
  recursion} in a similar fashion. To do so, we introduce a module
|General|. The module is parametrized by parametrized by two types |I|
and |O| and will be used to capture recursive calls to a function of
type | I -> O|:\footnote{This can be readily generalized to
  \emph{dependent functions} of type |(i : I) -> O i|, but we will not
    need this in the examples covered here.}

\begin{code}
module General (I : Set) (O : Set) where  
\end{code}


%if style == newcode
\begin{code}
  open Free  
\end{code}
%endif

To represent such calls, we define a single command, corresponding to
making a recursive call on an argument |i : I| and receiving a
response of type |O i|:

> data C : Set where
>   Call : I -> C
>
> R : C -> Set
> R (Call x) = O
>
> Rec : Set -> Set
> Rec = Free C R

Once again, we can define a smart constructor to make it a bit easier
to define recursive functions.

> call : I -> Rec O
> call i = Step (Call i) Pure

There are many different handlers that we can use: generating a
coinductive trace, unfolding a fixed number of calls, calculating
Bove-Capretta predicates, or providing a proof of
well-foundedness. Here, we will take a slightly different approach,
requiring that all recursive calls satisfy an \emph{invariant} to
ensure that a given property of the output holds:

> handle : (Inv : I -> O -> Set) (P : O -> Set) -> Rec O -> Set
> handle Inv P (Pure x)           = P x
> handle Inv P (Step (Call x) k)  = (o : O) -> Inv x o -> handle Inv P (k o)

\todo{Soundness?}

\subsection*{Example: quickSort}
\label{quicksort}

%if style == newcode
\begin{code}
module QS where  
  open Free
\end{code}
%endif

To illustrate how to reason with these invariants, we will show how to
reason about a function that is not structurally recursive, namely
|quickSort|. To do so, we import the |General| module, fixing the type
of our |quickSort| function


> open General (Pair (Nat -> Bool) (List Nat)) (List Nat)

\begin{code}  
    qs : List Nat -> Rec (List Nat)
    qs Nil = return Nil
    qs (Cons x xs) =
       call (<=-dec x , filter (<=-dec x) xs) >>= \lts ->
       call (>-dec x , filter (>-dec x) xs) >>= \gts ->
       return (lts ++ ([ x ] ++ gts))

    data IsSorted : List Nat -> Set where
      Base : IsSorted Nil
      Single : ∀ {x} -> IsSorted ([ x ])
      Step : ∀ {x y ys} -> So (<=-dec x y) -> IsSorted (Cons y ys) ->
        IsSorted (Cons x (Cons y ys))

    correct : (xs : List Nat) ->
      handle (\ { (p , is) o → Pair (IsSorted o) (all p o) }) IsSorted (qs xs)
    correct Nil = Base
    correct (Cons x xs) sxs (fst , snd) sys (fst₁ , snd₁) = {!!}
  
\end{code}


\section{Open questions}
\label{sec:questions}


\begin{itemize}
\item How can we use this technology to reason about combinations of
  effects? Eg mixing state and exceptions.

\item What about other effects? General recursion? Probablistic
  computations? Async/await?  Shift/reset?  Yield/fork?
  
\item How can we reason about compound computations built with |>>=|
  and |>>|?  There must be some 'law of consequence' that we can
  derive for specific handlers/effects -- is there a more general
  form?

\item  What is a specification of a program with effects? Can we define
  generalized refinement rules?

\item Relation with equations/equational part of algebraic effects?

\item Connection with relational specifications
  
\end{itemize}


\begin{acks}
I would like to thank my fans.  
\end{acks}

\nocite{*}
\bibliography{handlers.bib}


\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 


