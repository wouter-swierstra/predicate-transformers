\documentclass[acmsmall,screen]{acmart}\settopmatter{printfolios=true}

%include agda.fmt
%include handlers.fmt

%include preamble.tex

\begin{document}
\title[A predicate transformer semantics for effects]{A Predicate Transformer Semantics for Effects\\(Functional Pearl)}

\author{Wouter Swierstra}
\email{w.s.swierstra@@uu.nl}
\author{Tim Baanen}
\email{t.baanen@@uu.nl}
\affiliation{
  \institution{Universiteit Utrecht}
  \country{The Netherlands}
}
\authorsaddresses{Authors' address: Wouter Swierstra, w.s.swierstra@@uu.nl; Tim Baanen, t.baanen@@uu.nl}
% \acmBadgeR{artifacts_evaluated_functional.jpg}
\begin{abstract}
  Reasoning about programs that use effects can be much harder than
  reasoning about their pure counterparts. This paper presents a
  predicate transformer semantics for a variety of effects, including
  exceptions, state, non-determinism, and general recursion. The
  predicate transformer semantics gives rise to a refinement relation
  that can be used to relate a program to its specification, or even
  calculate effectful programs that are correct by construction.
\end{abstract}

\keywords{predicate transformers, effects, refinement, program
  calculation, weakest precondition semantics, programming with
  dependent types, free monads, Agda}

%include ccs.tex

\maketitle

\section{Introduction}
\label{sec:intro}

One of the key advantages of pure functional programming is
\emph{compositionality}. Pure programs may be tested in isolation;
referential transparency---the ability to freely substitute equals for
equals---enables us to employ equational reasoning to prove two
expressions equal~\cite{wadler-critique}. This has resulted in a rich
field of program calculation in the Bird-Meertens
style~\citep*{algebra-of-programming, pearls}, transforming an
inefficient executable specification to an efficient alternative
implementation.

Many programs, however, are \emph{not} pure, but instead rely on a
variety of effects, such as mutable state, exceptions,
general recursion, or non-determinism. Unfortunately, it is less clear
how to reason about such impure programs in a compositional fashion, as we can
no longer exploit referential transparency to reason about
subexpressions regardless of their context.

In recent years, \emph{algebraic effects} have emerged as a technique
to incorporate effectful operations in a purely functional
language~\cite{plotkin2002notions,pretnar2010logic}.  Algebraic
effects clearly separate the syntax of effectful operations and their
semantics, described by \emph{effect handlers}. In contrast to monad
transformers~\cite{liang-hudak-jones:transformers}, different effects
may be processed in any given order using a series of handlers.

This paper defines a predicate transformer semantics
for effectful programs, culminating in a constructive framework for
deriving verified effectful programs from their specifications, inspired by
existing work on program calculation in the refinement
calculus~\cite{back2012refinement,morgan1994programming}. We will
briefly sketch the key techniques, before illustrating them with
numerous examples throughout the remainder of the paper.

\begin{itemize}
\item The syntax of effectful computations may be represented
  by a free monad in type theory. Assigning meaning to such
  free monads amounts to assigning meaning to the syntactic operations
  each effect provides.
\item In this paper, we show how to assign \emph{predicate transformer
    semantics} to computations arising from the Kleisli arrows on
  these free monads. This enables us to compute the weakest
  precondition associated with a given postcondition. By defining
  these semantics as a \emph{fold} over the free monad, we can
  establish \emph{compositionality} results, allowing us to decompose
  the verification of a large program into smaller parts. These
  results hold for \emph{any} semantics defined as a fold, provided
  the predicate transformers are \emph{monotone}.
\item Using these weakest precondition semantics, we can define a
  notion of \emph{refinement} on computations. We show how to use this
  refinement relation to show a program satisfies its specification,
  or indeed, \emph{calculate} a program from its specification. By
  allowing specifications to appear in the leaves of our free monad,
  we can mix operations and specifications, enabling the step by step
  refinement of a specification to a complete program.
\end{itemize}
These principles are applicable to a range of different effects,
including exceptions (Section~\ref{sec:maybe}), state
(Section~\ref{sec:state}), non-determinism
(Section~\ref{sec:non-det}), and general recursion
(Section~\ref{sec:recursion}). Each section is illustrated with
numerous examples, each selected for their portrayal of proof
principles rather than being formidable feats of
formalisation. Besides relating effectful programs to their
specification, we show how programs and specifications may be mixed
freely, allowing verified programs to be calculated from their
specification one step at a time (Section~\ref{sec:stepwise-refinement}).


The definitions, examples, theorems and proofs presented in this paper
have all been formally verified in the dependently typed programming
language Agda~\cite{agda}, but the techniques translate readily to
other proof assistants based on dependent types such as
Idris~\cite{brady} or Coq~\cite{coq}. 

\section{Background}
\label{sec:background}
%if style == newcode
\begin{code}
module Check where

open import Prelude hiding (map; all)
open import Level hiding (lift)

module Free where
\end{code}
%endif

\subsection*{Free monads}
\label{sec:free-monads}

We begin by defining a datatype for free monads in the style
of \citet{hancock-setzer-I, hancock-setzer-II}:
\begin{code}
  data Free (hidden(l : Level)) (C : Set) (R : C -> Set) (a : (SetL(l))) : (SetL(l)) where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
\end{code}
You may want to think of |C| as being the type of \emph{commands}. A
computation described by the free monad |Free C R| either returns a
result of type |a| or issues a command |c : C|. For each |c : C|,
there is a set of responses |R c|. The second argument of the |Step|
constructor corresponds to the continuation, describing how to proceed
after receiving a response of type |R c|. It is straightforward to
show that the |Free C R| datatype is indeed a monad:
\begin{code}
  map : (Forall (l l' C R)) (implicit(a : Set l)) (implicit(b : Set l')) (a -> b) -> Free C R a -> Free C R b
  map f (Pure x)    = Pure (f x)
  map f (Step c k)  = Step c (\ r -> map f (k r)) 

  return : (Forall (l C R)) (implicit(a : Set l)) a -> Free C R a
  return = Pure

  _>>=_ : (Forall (l l' C R)) (implicit(a : Set l)) (implicit(b : Set l')) Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x    >>= f  = f x
  Step c x  >>= f  = Step c (\ r -> x r >>= f)
\end{code}
%if style == newcode
\begin{code}
  infixr 20 _>>=_
  _>>_ : forall {l l' C R} {a : Set l} {b : Set l'} -> Free C R a -> Free C R b -> Free C R b
  c1 >> c2 = c1 >>= \_ -> c2

\end{code}
%endif
The examples of effects studied in this paper will be phrased in terms
of such free monads; each effect, described in a separate section,
chooses |C| and |R| differently, depending on its corresponding
operations. This choice of operations---as is usually the case for
algebraic effects---determines a syntax to which we must still assign
semantics~\cite{tensor}.


\subsection*{Weakest precondition semantics}

The idea of of associating weakest precondition semantics with
imperative programs has a rich history, dating back to
Dijkstra's Guarded Command Language~\citeyearpar{gcl}. In this section, we
recall the key notions that we will use throughout the remainder of
the paper.

There are many different ways to specify the behaviour of a function
|f : a -> b|. One might provide a reference implementation, define a
relation |R : a -> b -> Set|, or write contracts and test cases. In
this paper, we will, however, focus on \emph{predicate transformer
  semantics}. Where these predicate transformers traditionally relate
the state space of an (imperative) program, they can be readily
adapted to the functional setting.

In general, we will refer to values of type |a -> Set| as a
\emph{predicate} on the type |a|; \emph{predicate transformers} are
functions between such predicates. The most famous example of a
predicate transformer is the \emph{weakest precondition}, given by the
function |wp| below:
\begin{spec}
  wp : (f : a -> b) -> (b -> Set) -> (a -> Set)
  wp f P = \ x -> P (f x)
\end{spec}
The |wp| predicate transformer maps a function |f : a -> b| and a
desired postcondition on the function's output, |b -> Set|, to the
weakest precondition |a -> Set| on the function's input that ensures
the postcondition will be satisfied. Its definition, however, is
simply (reverse) function composition.

This notion of weakest precondition semantics is often too
restrictive. In particular, there is no way to specify that the output
is related in a particular way to the input. This can be addressed
easily enough by allowing the function |f| to be \emph{dependent},
yielding the following definition for weakest preconditions:
\begin{code}
  wp : (Forall(l l' l'')) (implicit(a : Set l)) (implicit(b : a -> Set l')) (f : (x : a) -> b x) -> ((x : a) -> b x -> (SetL(l''))) -> (a -> (SetL(l'')))
  wp f P = \ x -> P x (f x)
\end{code}
Although this type is a bit more complicated, |wp f| still maps a
predicate to a predicate---hence we refer to it as a predicate
transformer semantics for the function |f|. 

When working with predicates and predicate transformers, we will
sometimes use the following shorthand notation:
\begin{code}
  _⊆_ : (Forall (l')) (implicit(a : Set)) (a -> (SetL(l'))) -> (a -> (SetL(l'))) -> (SetL(l'))
  P ⊆ Q = ∀ x -> P x -> Q x  
\end{code}
Predicate transformer semantics give rise to a notion of
\emph{refinement}~\cite{back2012refinement,morgan1994programming}:
\begin{code}
  _⊑_ : (implicit(a : Set)) (implicit (b : a -> Set)) (pt1 pt2 : ((x : a) -> b x -> Set) -> (a -> Set)) -> (SetOne)
  pt1 ⊑ pt2 = forall P -> pt1 P ⊆ pt2 P
\end{code}
This refinement relation is defined between \emph{predicate
  transformers}. As we will assign predicate transformer semantics to both
programs and specifications, we can relate them using this refinement
relation. For example, we can use this refinement relation to show a
program satisfies its specification; or to show that one program is
somehow `better' than another, where the notion of `better' arises
from our choice of predicate transformer semantics.

It is straightforward to show that this refinement relation is both transitive and reflexive:
\begin{code}
  ⊑-trans  : (implicit (a : Set)) (implicit (b : a -> Set)) (implicit (P Q R : ((x : a) -> b x -> Set) -> (a -> Set))) P ⊑ Q -> Q ⊑ R -> P ⊑ R

  ⊑-refl   : (implicit (a : Set)) (implicit (b : a -> Set)) (implicit (P : ((x : a) -> b x -> Set) -> (a -> Set))) P ⊑ P  
\end{code}
%if style == newcode
\begin{code}
  ⊑-trans {a} {b} {P} {Q} {R} r1 r2 p x y = r2 p x (r1 p x y)
  ⊑-refl {a} {b} {P} p x H = H  
\end{code}
%endif

In a pure setting, this refinement relation is not particularly
interesting: the refinement relation corresponds to extensional
equality between functions. The following lemma follows from the
`Leibniz rule' for equality in intensional type theory:
\begin{spec}
  refinement : forall (f g : a -> b) ->
    (wp f ⊑ wp g) ^^ ↔ ^^ (forall x -> f x == g x)
\end{spec}
%if style == newcode
\begin{code}
  ⊑-eq : {a b : Set} ->
    (f g : a -> b) -> wp f ⊑ wp g -> (x : a) -> f x == g x
  ⊑-eq f g R x = R (\_ y -> f x == y) x refl 

  eq-⊑ :  {a b : Set} ->
    (f g : a -> b) -> ((x : a) -> f x == g x) ->  wp f ⊑ wp g
  eq-⊑ f g eq P x H with f x | g x | eq x
  ... | _ | _ | refl = H
\end{code}
%endif
In the impure setting, however, we will use different notions of
weakest precondition, which in turn lead to different notions of
refinement.

In the remainder of this paper, we will define predicate transformer
semantics for \emph{Kleisli arrows} of the form |a -> Free C R
b|. While we could use the |wp| function to assign semantics to these
computations directly, we are typically not interested in syntactic
equality between free monads---but rather want to study the semantics
of the effectful programs they represent. To define a predicate
transformer semantics for effects we need to define a function of the
following form:
\begin{center}
\begin{spec}
  pt : (a -> Set) -> (Free C R a -> Set)
\end{spec}
\end{center}
These functions show how to lift a predicate on the type |a| over an
effectful computation returning values of type |a|. The definition of
|pt| depends very much on the semantics we wish to assign to the
effects of the free monad; the coming sections will give many examples
of such semantics. Crucially, the choice of |pt| and our weakest
precondition semantics, |wp|, together give us a way to assign weakest
precondition semantics to Kleisli arrows representing effectful
computations. Using these semantics for effectful computations, we can
then specify, verify, and calculate effectful programs.

\section{Partiality}
\label{sec:maybe}
%if style == newcode
\begin{code}
module Maybe where
  open import Data.Nat public
    using
      (_+_; _>_; _*_
      )
    renaming
      ( ℕ to Nat
      ; zero to Zero
      ; suc to Succ
      )
  open import Data.Nat.DivMod using (_div_)
  open import Data.Nat.Properties using (*-zeroʳ)        
  open Free      
\end{code}
%endif

We can define the datatype for |Partial| computations, corresponding to
the |Maybe| monad, by making the following choice for commands |C| and
responses |R| in our |Free| datatype:
\begin{code}
  data C : Set where
    Abort : C

  R : C -> Set
  R Abort = ⊥

  Partial : Set -> Set
  Partial = Free C R
\end{code}
There is a single command, |Abort|; there is no continuation after
issuing this command, hence there are no valid responses, as denoted
by |⊥|, the empty type. It is sometimes convenient to define a smart
constructor for failure:
\begin{code}
  abort  : (Forall(a)) Partial a
  abort  = Step Abort (\ ())
\end{code}
A computation of type |Partial a| will either return a value of type
|a| or fail, issuing the |abort| command. Note that the responses to
the |Abort| command are empty; the smart constructor |abort| uses this
to discharge the continuation in the second argument of the |Step|
constructor. Such smart constructors are sometimes referred to as
\emph{generic effects} in the algebraic effects literature~\cite{plotkin-power-2003}.
With the syntax in place, we can turn our attention to
verifying programs using a suitable predicate transformer semantics.


\subsection*{Example: division}

We begin by defining a small expression language, closed under
division and natural numbers:

\begin{code}
  data Expr : Set where
    Val : Nat -> Expr
    Div : Expr -> Expr -> Expr
\end{code}
We can specify the semantics of this language using an inductively
defined \emph{relation}:
\begin{code}
  data _⇓_ : Expr -> Nat -> Set where
    Base : (Forall(x)) Val x ⇓ x
    Step : (Forall(l r v1 v2)) l ⇓ v1 -> r ⇓ (Succ v2) -> Div l r ⇓ (v1 div (Succ v2))
\end{code}
In this definition, we rule out erroneous results by requiring that
the divisor always evaluates to a non-zero value.

Alternatively we can evaluate expressions by defining a
\emph{monadic} interpreter, using the |Partial| monad to handle
division-by-zero errors:
\begin{code}
  ⟦_⟧ : Expr -> Partial Nat
  ⟦ Val x ⟧      =  return x
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    v1 ÷ v2
\end{code}
%if style == newcode
\begin{code}                  
    where
\end{code}
%endif
This interpreter uses the following division operator that may fail
when the divisor is |Zero|:
\begin{code}  
                      _÷_ : Nat -> Nat -> Partial Nat
                      n ÷ Zero      = abort
                      n ÷ (Succ k)  = return (n div (Succ k))
\end{code}
The division operator from the standard library (|div|) requires an
implicit proof that the divisor is non-zero. In the case when the
divisor is |Zero|, we fail explicitly using |abort|.


How can we relate these two definitions? We can assign a weakest
precondition semantics to Kleisli arrows of the form |a -> Partial b|
as follows:
\begin{code}
  wpPartial : (implicit (a : Set)) (implicit (b : a -> Set)) (f : (x : a) -> Partial (b x)) -> (P : (x : a) -> b x -> Set) -> (a -> Set)
  wpPartial f P = wp f (mustPT P)
    where
    mustPT : (Forall(a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> Partial (b x) -> Set
    mustPT P _ (Pure y)          = P _ y
    mustPT P _ (Step Abort _)    = ⊥
\end{code}
To call the |wp| function we defined previously, we need to show how
to transform a predicate |P : b -> Set| to a predicate on partial
results, |Partial b -> Set|.  To do so, we define the auxiliary
function |mustPT|; the proposition |mustPT P c| holds when a
computation |c| of type |Partial b| successfully returns a value of
type |b| that satisfies |P|. The predicate transformer semantics we
wish to assign to partial computations is determined by how we define
|mustPT|. In this case, we wish to rule out failure entirely; hence
the case for the |Abort| constructor returns the empty
type. Alternatively, we could consider a different semantics for
partiality, such as requiring that computations fail or return a
result satisfying some desired property. As we shall see in the rest
of this paper, there is often some freedom to choose different
semantics for a single effect.

Now that we have a predicate transformer semantics for Kleisli arrows
in general, we can study the semantics of our monadic interpreter. To
do so, we pass the interpreter, |⟦_⟧|, and desired postcondition,
|_⇓_|,  as arguments to |wpPartial|:
\begin{center}
\begin{spec}
  wpPartial ⟦_⟧ _⇓_ : Expr -> Set
\end{spec}
\end{center}
This results in a predicate on expressions. For all expressions
satisfying this predicate, we know that the monadic interpreter and
the relational specification, |_⇓_|, must agree on the result of
evaluation. 

But what does this tell us about the correctness of our interpreter?
To understand the resulting predicate better, we might consider
manually defining our own predicate on expressions:
\begin{code}
  SafeDiv : Expr -> Set
  SafeDiv (Val x)       = ⊤
  SafeDiv (Div e1 e2)   = (e2 ⇓ Zero -> ⊥) ∧ SafeDiv e1 ∧ SafeDiv e2
\end{code}
We would expect that any expression |e| for which |SafeDiv e| holds
can be evaluated without encountering a division-by-zero
error. Indeed, we can prove that |SafeDiv| is a sufficient condition
for our two notions of evaluation to coincide:
\begin{code}
  correct : SafeDiv ⊆ wpPartial ⟦_⟧ _⇓_
\end{code}
%if style == newcode
\begin{code}
  correct (Val x) h = Base
  correct (Div e1 e2 ) (nz , (h1 , h2)) with ⟦ e1 ⟧ | ⟦ e2 ⟧ | correct e1 h1 | correct e2 h2
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure v1 | Pure Zero | ih1 | ih2 = magic (nz ih2)
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure v1 | Pure (Succ v2) | ih1 | ih2 = Step ih1 ih2
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure x | Step Abort x₁ | ih1 | ()
  correct (Div e1 e2) (nz , (h1 , h2)) | Step Abort x | v2 | () | ih2
\end{code}
%endif
This lemma relates the two semantics, expressed as a relation and an
evaluator, for those expressions that satisfy the |SafeDiv| property.

We may not want to define predicates such as |SafeDiv|
ourselves. Instead, we can define the more general predicate
characterising the \emph{domain} of a partial function:
\begin{code}
  dom : (implicit(a : Set)) (implicit (b : a -> Set)) ((x : a) -> Partial (b x)) -> (a -> Set)
  dom f = wpPartial f (\ _ _ -> ⊤)
\end{code}
Once again, we can show that the two semantics agree precisely on the
domain of the interpreter.
\begin{code}
  sound     : dom ⟦_⟧            ^^ ⊆ ^^ wpPartial ⟦_⟧ _⇓_
  complete  : wpPartial ⟦_⟧ _⇓_  ^^ ⊆ ^^ dom ⟦_⟧
\end{code}
%if style == newcode
\begin{code}
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

  aux : (e : Expr) (v : Nat) -> ⟦ e ⟧ ≡ Pure v -> e ⇓ v
  aux e v eq with sound e (inDom e eq) 
  ... | H rewrite eq = H

  wpPartial1 : {e1 e2 : Expr} -> wpPartial ⟦_⟧ _⇓_ (Div e1 e2) -> wpPartial ⟦_⟧ _⇓_ e1
  wpPartial1 {e1} {e2} h with ⟦ e1 ⟧ | inspect ⟦_⟧ e1 | ⟦ e2 ⟧
  wpPartial1 {e1} {e2} () | Pure x | eq | Pure Zero
  wpPartial1 {e1} {e2} h | Pure x | [[[ eq ]]] | Pure (Succ y) = aux e1 x eq
  wpPartial1 {e1} {e2} () | Pure x | eq | Step Abort x₁
  wpPartial1 {e1} {e2} () | Step Abort x | eq | ve2

  wpPartial2 : {e1 e2 : Expr} -> wpPartial ⟦_⟧ _⇓_ (Div e1 e2) -> wpPartial ⟦_⟧ _⇓_ e2
  wpPartial2 {e1} {e2} h with ⟦ e1 ⟧ | inspect ⟦_⟧ e1 | ⟦ e2 ⟧ | inspect ⟦_⟧ e2
  wpPartial2 {e1} {e2} h | Pure x | [[[ eqx ]]] | Pure y | [[[ eqy ]]] = aux e2 y eqy
  wpPartial2 {e1} {e2} () | Pure x | [[[ eq ]]] | Step Abort x₁ | eq2
  wpPartial2 {_} {_} () | Step Abort x | eq1 | se2 | eq2

  complete (Val x) h = tt
  complete (Div e1 e2) h
    with ⟦ e1 ⟧ | inspect ⟦_⟧ e1 | ⟦ e2 ⟧ | inspect ⟦_⟧ e2
      | complete e1 (wpPartial1 {e1} {e2} h)
      | complete e2 (wpPartial2 {e1} {e2} h)
  complete (Div e1 e2) h | Pure x | [[[ eqx ]]] | Pure Zero | [[[ eqy ]]] | p1 | p2
    rewrite eqx | eqy = magic h
  complete (Div e1 e2) h | Pure x | [[[ eqx ]]] | Pure (Succ y) | [[[ eqy ]]] | p1 | p2 = tt
  complete (Div e1 e2) h | Pure x | eq1 | Step Abort x₁ | eq2 | p1 | ()
  complete (Div e1 e2) h | Step Abort x | eq1 | se2 | eq2 | () | p2
\end{code}
%endif
Both proofs proceed by induction on the argument expression; despite
the necessity of a handful of auxiliary lemmas, they are
fairly straightforward.

\subsection*{Refinement}

The weakest precondition semantics on partial computations defined
above give rise to a refinement relation on Kleisli arrows of the
form |a -> Partial b|. We can characterise this relation by proving
the following lemma:
\begin{spec}
  refinement : (f g : a -> Partial b) ->
    (wpPartial f ^^ ⊑ ^^ wpPartial g) ^^ ↔ ^^  (forall x -> (f x == g x) ∨ (f x == abort))
\end{spec}
Why care about this refinement relation? Not only can we use it to
relate Kleisli morphisms, but it can also relate a program to a
specification given by a pre- and postcondition, as we shall see
shortly.

\subsection*{Example: \textsc{Add}}

Suppose we are writing an interpreter for a simple stack machine. To
interpret the |ADD| instruction, we replace the top two elements of
the stack with their sum; this may fail if the stack has
too few elements. This section shows how to prove that the obvious
definition meets its specification.

We begin by defining a notion of specification in terms of a pre- and
postcondition. In general, the specification of a function of type |(x
: a) -> b x| consists of a precondition on |a| and a postcondition
relating inputs that satisfy this precondition and the corresponding outputs:

\begin{code}
  record Spec (hidden(l : Level)) (a : Set) (b : a -> Set) : (SetL(suc l)) where
    constructor [[_,_]]
    field
      pre   : a -> (SetL(l))
      post  : (x : a) -> b x -> (SetL(l))
\end{code}
As is common in the refinement calculus literature, we will write |[[
P , Q ]]| for the specification consisting of the precondition |P| and
postcondition |Q|. In many of our examples, the type |b| does not
depend on |x : a|, motivating the following type synonym:
\begin{code}
  SpecK : (implicit(l : Level)) Set -> Set -> (SetL(suc l))
  SpecK a b = Spec a (K b)
\end{code}
This definition uses the combinator K to discard the unused argument
of type |a|.

Using this definition, we can define the following specification for
our addition function:
\begin{code}
  data Add : List Nat -> List Nat -> Set where
    AddStep : (implicit(x1 x2 : Nat)) (implicit(xs : List Nat)) Add (x1 :: x2 :: xs) ((x1 + x2) :: xs)

  addSpec : SpecK (List Nat) (List Nat)
  addSpec = [[ (\ xs -> length xs > 1) , Add ]]
\end{code}
That is, provided we are given a list with at least two elements, we
should replace the top two elements with their sum. Here we describe
the desired postcondition by introducing a new datatype, |Add|,
relating the input and output stacks.

How can we relate this specification to an implementation? We have
seen how the |wpPartial| function assigns predicate transformer
semantics to functions---but we do not yet have a corresponding
predicate transformer \emph{semantics} for our specifications. The
|wpSpec| function does precisely this:
\begin{code}
  wpSpec : (Forall(l a)) (implicit(b : a -> Set)) Spec (hidden(l)) a b -> (P : (x : a) -> b x -> (SetL(l))) -> (a -> (SetL(l)))
  wpSpec [[ pre , post ]] P = \ x -> (pre x) ∧ (post x ⊆ P x)
\end{code}
Given a specification, |Spec a b|, the |wpSpec| function computes the
weakest precondition necessary to satisfy an arbitrary postcondition
|P|: namely, the specification's precondition should hold and its
postcondition must imply |P|.

Using this definition we can precisely formulate the problem at
hand: can we find a program |add : List Nat -> Partial (List
Nat)| that refines the specification given by |addSpec|:
\begin{spec}
  correctnessAdd : wpSpec addSpec ⊑ wpPartial add
\end{spec}
Defining such a program and verifying its correctness is entirely
straightforward:
\begin{code}
  pop : (Forall (a)) List a -> Partial (a × List a)
  pop Nil        = abort
  pop (x :: xs)  = return (x , xs)

  add : List Nat -> Partial (List Nat)
  add xs =
    pop xs >>= \{ (x1 , xs) -> 
    pop xs >>= \{ (x2 , xs) ->
    return ((x1 + x2) :: xs)}}
\end{code}
%if style == newcode
\begin{code}
  correctnessAdd : wpSpec addSpec ⊑ wpPartial add  
  correctnessAdd P Nil (() , _)
  correctnessAdd P (x :: Nil) (Data.Nat.s≤s () , _)
  correctnessAdd P (x :: y :: xs) (_ , H) = H (x + y :: xs) AddStep
\end{code}
%endif
We include this example here to illustrate how to use the refinement
relation to relate a \emph{specification}, given in terms of a pre-
and postcondition, to its implementation. When compared to the
refinement calculus, however, we have not yet described how to mix
code and specifications---a point we will return to later
(Section~\ref{sec:stepwise-refinement}). Before doing so, however, we
will explore several other effects, their semantics in terms of
predicate transformers, and the refinement relation that arises from
these semantics.

\subsection*{Alternative semantics}
\label{alternative-abort}

The predicate transformers arising from the |wpPartial| function are
not the only possible choice of semantics. In particular, sometimes we
may use the |Abort| command to `short-circuit' a computation and
handle the corresponding exception. This section explores how to adapt
our definitions accordingly.

Suppose we have a function that computes the product of the numbers
stored in a list:
\begin{code}
  product : List Nat -> Nat
  product = foldr _*_ 1
\end{code}
If this list contains a zero, we can short circuit the computation and
return zero immediately. To do so, we define the following
computation:
\begin{code}
  fastProduct : List Nat -> Partial Nat
  fastProduct Nil                 = return 1
  fastProduct (Zero :: xs)        = abort
  fastProduct (k :: xs)           = map (_*_ k) (fastProduct xs)
\end{code}
To run this computation, we provide a handler that maps |abort| to
some default value.
\begin{code}
  defaultHandler : (Forall(a)) a -> Partial a -> a
  defaultHandler _ (Pure x)          = x
  defaultHandler d (Step Abort _)    = d
\end{code}

Now the question arises how to assign a suitable predicate transformer
semantics to the |fastProduct| function. We could choose to use the
|wpPartial| function we defined previously; doing so, however, would
require the input list to not contain any zeros. It is clear that we
want to assign a different semantics to our aborting computations. To
do so, we provide the following |wpDefault| function that requires the
desired postcondition |P| holds of the default value when the
computation aborts:
\begin{code}
  wpDefault : (Forall (a b : Set)) (d : b) -> (f : a -> Partial b) -> (P : a -> b -> Set) -> (a -> Set)
  wpDefault (hidden(a)) (hidden(b)) d f P = wp f defaultPT
    where
    defaultPT : (x : a) -> Partial b -> Set
    defaultPT x (Pure y)        = P x y 
    defaultPT x (Step Abort _)  = P x d
\end{code}

The |wpDefault| function computes \emph{some} predicate on the
function's input. But how do we know that this predicate is meaningful
in any way? We could compute simply return a trivial predicate that is
always holds. To relate the predicate transformer semantics to the
|defaultHandler| we need to prove the following soundness result:
\begin{code}
  soundness : (Forall (a b)) (P : a -> b -> Set) -> (d : b) -> (c : a -> Partial b) ->
    forall x -> wpDefault d c P x -> P x (defaultHandler d (c x))
\end{code}
%if style == newcode
\begin{code}
  soundness P d c x H with c x
  soundness P d c x H | Pure y = H
  soundness P d c x H | Step Abort _ = H
\end{code}
%endif
Put simply, this soundness result ensures that whenever the
precondition computed by |wpDefault| holds, the output returned by
running the |defaultHandler| satisfies the desired postcondition.

Now we can finally use our refinement relation to relate the
|fastproduct| function to the original |product| function:
\begin{code}
  correctnessProduct : wp product ⊑ wpDefault 0 fastProduct
\end{code}
%if style == newcode
\begin{code}
  correctnessProduct   P Nil H = H
  correctnessProduct   P (Zero :: xs) H = H
  correctnessProduct   P (Succ x :: xs) H
    with fastProduct xs | correctnessProduct (\xs v -> P (Succ x :: xs) _) xs H
  correctnessProduct   P (Succ x :: xs) H | Pure v | IH  = IH
  correctnessProduct   P (Succ x :: xs) H | Step Abort _ | IH rewrite *-zeroʳ x = IH
\end{code}
%endif

This example shows how to prove soundness of our predicate transformer
semantics with respect to a given handler. The predicate transformers, such as
|wpDefault| and |wpPartial|, return \emph{some} predicate; by proving such soundness
results, we can ensure that the
semantics is meaningful. Furthermore, this example shows how different
choices of handler may exist for the \emph{same} effect---a point we shall
return to when discussing non-determinism (Section~\ref{sec:non-det}).


\section{Mutable state}
\label{sec:state}

%if style == newcode
\begin{code}
module State (s : Set) where
  open Free
  open Maybe using (SpecK; Spec; [[_,_]]; wpSpec)
\end{code}
%endif

In this section, we will explore how to develop similar predicate
transformer semantics for mutable state, giving rise to a familiar
Hoare logic. In what follows, we will assume a fixed type |s : Set|,
representing the type of the state. As before, we can define the
desired free monad in terms of commands |C| and responses |R|:
\begin{code}
  data C : Set where
    Get : C
    Put : s -> C

  R : C -> Set
  R Get      = s
  R (Put _)  = ⊤

  State : (Forall(l)) (SetL(l)) -> (SetL(l))
  State = Free C R
\end{code}
To facilitate writing stateful computations, we can define a pair of
smart constructors:
\begin{code}
  get : State s
  get = Step Get return

  put : s -> State ⊤
  put s = Step (Put s) (\_ -> return tt)
\end{code}
The usual handler for stateful computations maps our free monad,
|State s|, to the state monad:
\begin{code}
  run : (implicit(a : Set)) State a -> s -> a × s
  run (Pure x)           s  = (x , s)
  run (Step Get k)       s  = run (k s) s
  run (Step (Put s) k)   _  = run (k tt) s
\end{code}
Inspired by the previous section, we can define the following
predicate transformer that for every stateful computation of type
|State b|, maps a postcondition on |b × s| to the required
precondition on the initial state of type |s|:
\begin{code}
  statePT : (Forall(l l')) (implicit(b : Set l)) (b × s -> (SetL(l'))) -> State b -> (s -> (SetL(l')))
  statePT P (Pure x)               = \ s  -> P (x , s)
  statePT P (Step Get k)           = \ s  -> statePT P (k s) s
  statePT P (Step (Put s) k)       = \ _  -> statePT P (k tt) s
\end{code}
We can generalise this predicate transformer slightly. As we saw
before, we sometimes describe postconditions as a \emph{relation}
between inputs and outputs. In the case for stateful computations,
this amounts to allowing the postcondition to also refer to the
initial state:
%{
%if style == poly
%format statePTR = statePT"^\prime"
%else
%format statePTR = statePT'
%endif
\begin{code}
  statePTR : (Forall(l l')) (implicit(b : Set l))  (s -> b × s -> (SetL(l'))) -> State b -> (s -> (SetL(l')))
  statePTR P c i = statePT (P i) c i
\end{code}
In the remainder of this section, we will overload the variable name
|statePT| to refer to both variations of the same function; the
context should disambiguate the version being used.

Finally, we can define a weakest precondition semantics for Kleisli
morphisms of the form |a -> State b|:
%}
\begin{code}
  wpState : (Forall(l l' l'')) (implicit(a : Set l)) (implicit(b : Set l'))  (a -> State b) -> (P : a × s -> b × s -> (SetL(l''))) -> (a × s -> (SetL(l'')))
  wpState f P (x , i) = wp f ((hiddenConst (\ c -> statePT' (\ j -> P (x , j)) c i))) x
\end{code}
Given any predicate |P| relating the input, initial state, final state
and result of the computation, the |wpState| function computes the
weakest precondition required of the input and initial state to ensure
|P| holds upon completing the computation. The definition amounts to
composing the |wp| and |statePT| functions we have seen previously.
As we did in the previous section for |wpDefault|, we can prove
soundness of this semantics with respect to the |run| function:
\begin{code}
  soundness : (Forall(a b : Set)) (P : a × s -> b × s -> Set) -> (f : a -> State b) -> 
    forall i x -> wpState f P (x , i) -> P (x , i) (run (f x) i)
\end{code}
%if style == newcode           
\begin{code}
  soundness {a} {b} P c i x H = lemma i (c x) H
    where
    lemma : (st : s) -> (statec : State b) -> (statePT (P (x , i)) statec st) -> P (x , i) (run statec st)
    lemma i (Pure y) H = H
    lemma i (Step Get k) H = lemma i (k i) H
    lemma i (Step (Put s) k) H = lemma s (k tt) H
\end{code}
%endif

\subsection*{Example: tree labelling}
\label{sec:trees}
%if style == newcode
\begin{code}
module Relabel where
  open Free
  open Maybe using (Spec; SpecK; [[_,_]]; wpSpec)
  open import Data.Nat public
    using
      (_+_; _>_; _*_
      )
    renaming
      ( ℕ to Nat
      ; zero to Zero
      ; suc to Succ
      )
  module StateNat = State Nat
  open StateNat
\end{code}
%endif

To show how to reason about stateful programs using our weakest
precondition semantics, we revisit a classic verification problem
proposed by \citet{hutton2008reasoning}: given a binary tree as input,
relabel this tree so that each leaf has a unique number associated
with it. A typical solution uses the state monad to keep track of the
next unused label. The challenge that \citeauthor{hutton2008reasoning}
pose is to reason about the program, without expanding the definition
of the monadic operations.

We begin by defining the type of binary trees:
\begin{code}
  data Tree (a : Set) : Set where
    Leaf  : a -> Tree a
    Node  : Tree a -> Tree a -> Tree a
\end{code}
%if style == newcode
\begin{code}  
  flatten : ∀ {a} -> Tree a -> List a
  flatten (Leaf x)    = [ x ]
  flatten (Node l r)  = flatten l ++ flatten r

  size : ∀ {a} -> Tree a -> Nat
  size (Leaf x)    = 1
  size (Node l r)  = size l + size r

  seq : Nat -> Nat -> List Nat
  seq i Zero = Nil
  seq i (Succ n) = Cons i (seq (Succ i) n)
\end{code}
%endif
One obvious choice of specification might be the following:
\begin{code}
  relabelSpec : (Forall(a)) SpecK (Tree a × Nat) (Tree Nat × Nat)
  relabelSpec = [[ K ⊤ , relabelPost ]]
    where
      relabelPost : (Forall(a)) Tree a × Nat -> Tree Nat × Nat -> Set
      relabelPost (t , s) (t' , s') = (flatten t' == (seq (s) (size t))) ∧ (s + size t == s')
\end{code}
The precondition of this specification is trivially true regardless of
the input tree and initial state; the postcondition consists of a
conjunction of two auxiliary statements: first, flattening the
resulting tree |t'| produces the sequence of numbers from |s| to |s +
size t|, where |t| is the initial input tree; furthermore, the output
state |s'| should be precisely |size t| larger than the input state
|s|. Note that our |size| function only counts the number of leaves,
as these are only of interest for relabelling.

We can now define the obvious relabelling function as follows:
%if style == newcode
\begin{code}
  fresh : State Nat
  fresh =  get >>= \ n ->
           put (Succ n) >>
           return n
\end{code}
%endif
\begin{code}         
  relabel : (Forall(a)) Tree a -> State (Tree Nat)
  relabel (Leaf x)    = map Leaf fresh
  relabel (Node l r)  =
    relabel l >>= \ l' ->
    relabel r >>= \ r' ->
    return (Node l' r') 
\end{code}
Here the auxiliary function |fresh| increments the current state and
returns its value.

Next, we would like to show that this definition satisfies the
intended specification. To do so, we can use our |wpState| function to
compute the weakest precondition semantics of the relabelling
function and formulate the desired correctness property:
\begin{code}
  correctnessRelabel : (Forall(a : Set)) wpSpec (instantiate (relabelSpec)) ⊑ wpState relabel
\end{code}
The proof is interesting. Initially, it proceeds by induction on the
input tree. The base case for the |Leaf| constructor is easy enough to
discharge; the inductive case, however, poses a greater challenge. In
particular, we assume that the |wpSpec relabelSpec P| holds for some
arbitrary predicate |P|; the goal we wish to prove in the case for the
|Node| constructor amounts to proving the following statement:
\begin{center}
\begin{spec}
  statePT (P (Node l r , i)) (relabel l >>= (\ l' → relabel r >>= (\ r' → Pure (Node l' r')))) i
\end{spec}
\end{center}
At first glance, it is not at all obvious how to use our induction
hypothesis! Although we can use our induction hypothesis to show |P|
holds for |l| and |r|---it is not clear how to use this information to
prove the above goal, without knowing anything further about |P|.

\subsection*{Compositionality}
\label{sec:compositionality}
To complete the proof, we need an auxiliary lemma that enables us to
prove a property of a composite computation, |c >>= f|, in terms of
the semantics of |c| and |f|:
\begin{code}
  compositionality : (Forall(a b : Set)) (c : State a) (f : a -> State b) ->
    ∀ i P → statePT P (c >>= f) i == statePT (wpState f (hiddenConst(P))) c i
\end{code}
%if style == newcode
\begin{code}
  compositionality (Pure x) f i P = refl
  compositionality (Step Get k) f i P = compositionality (k i) f i P
  compositionality (Step (Put x) k) f i P = compositionality (k tt) f x P
\end{code}
%endif
Most predicate transformer semantics of imperative languages
have a similar rule, mapping sequential composition of programs to the
composition of their associated predicate transformers:
\begin{center}
\begin{spec}
wp(c1 ; c2, R) = wp(c1, wp(c2, R))  
\end{spec}
\end{center}
By defining semantics for Kleisli morphisms, |wpState|, in terms of
the predicate transformer semantics of computations, |statePT|, we can
prove this analogous result. The proof, by induction on the stateful
computation |c|, is trivial.

Using this compositionality property, we can massage the proof
obligation of our correctness lemma to the point where we can indeed
apply our induction hypotheses and complete the remaining proof
obligations.

%if style == newcode
\begin{code}
  correctnessRelabel = step2
    where
    open NaturalLemmas
    --  Simplify proofs of refining a specification,
    --  by first proving one side of the bind, then the second.
    --  This is essentially the first law of consequence,
    --  specialized to the effects of State and Spec.
    prove-bind : ∀ {a b} (mx : State a) (f : a → State b) P i →
      statePT (wpState f \ _ → P) mx i → statePT P (mx >>= f) i
    prove-bind mx f P i x = coerce {zero} (sym (compositionality mx f i P)) x
    prove-bind-spec : ∀ {a b} (mx : State a) (f : a → State b) spec →
      ∀ P i → (∀ Q → Spec.pre spec i × (Spec.post spec i ⊆ Q) → statePT Q mx i) →
      Spec.pre spec i × (Spec.post spec i ⊆ wpState f (\ _ → P)) →
      statePT P (mx >>= f) i
    prove-bind-spec mx f spec P i Hmx Hf = prove-bind mx f P i (Hmx (wpState f (\ _ → P)) Hf)

    --  Partially apply a specification.
    applySpec : ∀ {a b s} → SpecK {zero} (a × s) (b × s) → a → SpecK s (b × s)
    applySpec [[ pre , post ]] x = [[ (\ s → pre (x , s)) , (\ s → post (x , s)) ]]

    --  Ingredients for proving the postcondition holds.
    --  By abstracting over the origin of the numbers,
    --  we can do induction on them nicely.
    append-seq : ∀ a b c → seq a b ++ seq (a + b) c ≡ seq a (b + c)
    append-seq a Zero c = cong (\ a' → seq a' c) (sym (plus-zero a))
    append-seq a (Succ b) c = cong (Cons a) (trans
      (cong (\ a+b → seq (Succ a) b ++ seq a+b c) (+-succ a b))
      (append-seq (Succ a) b c))
    postcondition : ∀ s s' s'' sl fl sr fr →
      Pair (fl ≡ seq s sl) (s + sl ≡ s') →
      Pair (fr ≡ seq s' sr) (s' + sr ≡ s'') →
      Pair (fl ++ fr ≡ seq s (sl + sr)) (s + (sl + sr) ≡ s'')
    postcondition s .(s + sl) .(s + sl + sr) sl .(seq s sl) sr .(seq (s + sl) sr)
      (refl , refl) (refl , refl) = append-seq s sl sr , +-assoc s sl sr

    --  We have to rewrite the formulation of step2 slightly to make it acceptable for the termination checker.
    step2' : ∀ {a} P (t : Tree a) s → wpSpec relabelSpec P (t , s) → statePT (P (t , s)) (relabel t) s
    step2' P (Leaf x) s (fst , snd) = snd (Leaf s , Succ s) (refl , plus-one s)
    step2' P (Node l r) s (fst , snd) = prove-bind-spec (relabel l) _ (applySpec relabelSpec l) _ _
      (\ Q → step2' (\ _ → Q) l s)
      (tt , \ l',s' postL → let l' = Pair.fst l',s' ; s' = Pair.snd l',s'
        in prove-bind-spec (relabel r) _ (applySpec relabelSpec r) _ _
          (\ Q → step2' (\ _ → Q) r s')
          (tt , \ r',s'' postR → let r' = Pair.fst r',s'' ; s'' = Pair.snd r',s''
            in snd (Node l' r' , s'') (postcondition s s' s'' (size l) (flatten l') (size r) (flatten r') postL postR)))
    step2 : wpSpec relabelSpec ⊑ wpState relabel
    step2 P (t , s) (fst , snd) = step2' P t s (fst , snd)
\end{code}
%endif

At this point, it is worth pointing out that this compositionality
property does not hold exclusively for stateful computations. In fact,
we can prove a more general result that holds for \emph{any} predicate
transformer semantics |pt| defined as a fold over the free monad:
%if style == newcode
\begin{code}
module Compositionality
  (C : Set) (R : C -> Set) (ptalgebra : (c : C) -> (R c -> Set) -> Set)
  where
  open Free
  open Maybe using (wpSpec; [[_,_]])

  postulate
    ext : {l l' : Level} {a : Set l} {b : Set l'} -> {f g : a -> b} ->
      ((x : a) -> f x ≡ g x) -> f ≡ g

  pt : {a : Set} -> Free C R a -> (a -> Set) -> Set
  pt (Pure x) P = P x
  pt (Step c x) P = ptalgebra c (\r -> pt (x r) P)

  wpCR : {a : Set} {b : a -> Set} ->
      ((x : a) -> Free C R (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpCR f P x = pt (f x) (P x)
\end{code}
%endif
\begin{code}
  compositionality : (Forall(a b : Set)) (c : Free C R a) (f : a -> Free C R b) ->
    ∀ P -> pt (c >>= f) P ≡ pt c (wpCR f (hiddenConst(P)))
\end{code}
Note that this proof requires that the semantics of Kleisli morphisms,
|wpCR|, is defined in terms of the predicate transformer |pt|. If we
restrict ourselves to Kleisli arrows, however, we can formulate similar
properties even more succinctly.
%if style == newcode
\begin{code}
  compositionality (Pure x) f P = refl
  compositionality (Step c x) f P =
    cong (\h -> ptalgebra c h) (ext (\r -> compositionality (x r) f P))
\end{code}
%endif  
First, we can define the usual composition of Kleisli morphisms as follows:
\begin{code}
  _>=>_ : (Forall(l l' l'')) (implicit(a : Set l)) (implicit(b : Set l')) (implicit(c : Set l'')) (Forall(C R)) (a → Free C R b) -> (b → Free C R c) -> a → Free C R c
  f >=> g = \ x → f x >>= g
\end{code}
Using this composition operator, we can show that for \emph{any}
compositional predicate transformer semantics, the following
property holds:
\begin{code}
  compositionality-left : (Forall(a b c : Set)) (f1 f2 : a -> Free C R b) (g : b -> Free C R c) ->
    wpCR f1 ⊑ wpCR f2 ->
    wpCR (f1 >=> g) ⊑ wpCR (f2 >=> g)
\end{code}
%if style == newcode
\begin{code}
  compositionality-left mx my f H P x y
    rewrite compositionality (mx x) f (P x)
    | compositionality (my x) f (P x) =
     H (\x y -> pt (f y) (P x)) x y
\end{code}
%endif
This is a central result of our development---it shows how the
compositionality of any weakest precondition semantics is respected
when considering refinement proofs. These results establish that these predicate
transformers form an \emph{ordered monad}~\cite{ordered}.
Just as referential transparency
guarantees that \emph{pure} expressions may be substituted freely
during equational reasoning, this lemma guarantees that predicate
transformers may be substituted freely during refinement proofs. It is worth
repeating that this lemma holds for \emph{any} predicate transformer
semantics defined as a fold over a free monad.

A similar property also holds when considering refinements on the
second argument of a Kleisli composition.
\begin{code}
  compositionality-right : (Forall(a b c)) (f : a -> Free C R b) (g1 g2 : b -> Free C R c) ->
    wpCR g1 ⊑ wpCR g2 ->
    wpCR (f >=> g1) ⊑ wpCR (f >=> g2)
  \end{code}    
%if style == newcode
  \begin{code}
  postulate
\end{code}
%endif
This second property, however, only holds under the assumption that
the predicate transformers computed over a free monad are
\emph{monotone}, that is to say, the function |pt| satisfies the
following property:
\begin{code}
    monotonicity : (Forall(a)) (implicit(P Q : a -> Set)) P ⊆ Q -> (c : Free C R a) -> pt c P -> pt c Q      
\end{code}
%if style == newcode
\begin{code}
  compositionality-right mx f g H P x wp1
    rewrite compositionality (mx x) f (P x)
    | compositionality (mx x) g (P x) = monotonicity (H _) (mx x) wp1 
  \end{code}
%endif  
  This monotonicity property holds of all the predicate transformers
  presented in this paper and is straightforward to prove for all of them.

\subsection*{Rule of consequence}
\label{sec:consequence}

This example illustrates how reasoning about programs written using
the state monad give rise to the typical pre- and postcondition
reasoning found in the verification of imperative programs. Indeed, we
can also show that the familiar laws for the weakening of preconditions and
strengthening of postconditions also hold:
\begin{code} 
  weakenPre          : (implicit(a : Set)) (implicit(b : a -> Set)) (implicit(P P' : a -> Set)) (implicit(Q : (x : a) -> b x -> Set)) (P ⊆ P') -> (wpSpec [[ P , Q ]] ⊑ wpSpec [[ P' , Q ]])

  strengthenPost     : (implicit(a : Set)) (implicit(b : a -> Set)) (implicit(P : a -> Set)) (implicit(Q Q' : (x : a) -> b x -> Set)) (forall (x : a) -> Q' x ⊆ Q x) -> (wpSpec [[ P , Q ]] ⊑ wpSpec [[ P , Q' ]])
\end{code}
%if style == newcode
\begin{code}
  weakenPre H1 p H2 (pre , post) = (H1 H2 pre , post)  
  strengthenPost H1 p H2 (pre , post) = (pre , \ x y → post x (H1 _ x y))  
\end{code}
%endif
Such laws are particularly useful when `bookkeeping' large proof
obligations that can sometimes arise during program verification.

\subsection*{Equations}

%if style == newcode
\begin{code}
module Laws (s : Set) where
  open Free
  open Maybe using (SpecK; Spec; [[_,_]]; wpSpec)
  module StateS = State s
  open StateS
  postulate
    a : Set
    k0 : State a
    k1 : s -> State a
    k2 : s -> s -> State a    
    x y : s
\end{code}
%endif


Typically the intended semantics of algebraic effects is given by
means of \emph{equations}, identifying syntactically different
terms. Indeed, the genesis of algebraic effects can be found in the
work by \citet{plotkin2002notions}, that identified a handful of
equations on relating |get| and |put| operations that completely
determined the state monad. How do these equations relate to the
weakest precondition semantics presented here? 

Firstly, we can define the following equivalence relation between
stateful computations:
\begin{code}
  _≃_ : (Forall(b : Set)) State b  -> State b -> SetOne
  t1 ≃ t2 = (wpState' t1 ⊑ wpState' t2) ∧ (wpState' t2 ⊑ wpState' t1)
    where
    wpState' : (Forall(b)) State b -> (P : s -> b × s -> Set) -> (s -> Set)
\end{code}
%if style == newcode  
\begin{code}
    wpState' {b} t P s = wpState {a = ⊤} {b} (\ _ -> t) (\ { (tt , s') y → P s' y}) (tt , s)
\end{code}
%endif
Here we define a degenerate instance of the previous |wpState| function
that works on terms of type |State b| rather than Kleisli arrows |a ->
State b|. To do so, we simply call the previous semantics,
instantiating the type variable |a| to the unit type.

To establish that an equation between two terms |t1| and |t2| holds
with respect to the |wpState| semantics, amounts to proving that |t1
≃ t2|. For example, the following four laws follow immediately from
our definitions for all |k|, |x|, and |y|:
%{
%if style == poly
%format k0 = k
%format k1 = k
%format k2 = k
%endif
\begin{spec}
  law1 : k0 ≃ (get >>= \ s -> put s >> k0)
  law2 : (get >>= \ s1 -> get >>= \ s2 -> k2 s1 s2) ≃ (get >>= \ s -> k2 s s)
  law3 : (put y >> (put x >> k0)) ≃ (put x >> k0)
  law4 : (put x >> (get >>= k1)) ≃ (put x >> k1 x)
\end{spec}
%}
%if style == newcode
\begin{spec}
  law1 = (\ P x H → H) , (\ P x H → H)
  law2 = (\ P x H → H) , (\ P x H → H)
  law3 = (\ P x H → H) , (\ P x H → H)
  law4 = (\ P x H → H) , (\ P x H → H)  
\end{spec}
%endif
More generally, we can use such an equivalence relation to verify that
the predicate transformer semantics respect a set of equations
that are expected to hold for a given algebraic effect.

\section{Non-determinism}
\label{sec:non-det}

Can we repeat this construction of predicate transformer semantics for
other effects? In this section, we will show how we can define a
weakest precondition semantics for non-deterministic
computations. Once again, we begin by defining a free monad describing
the effects that can be used to describe such
computations:

%if style == newcode
\begin{code}
module Nondeterminism where

  open Free hiding (_⊆_)
  open Maybe using (wpSpec; SpecK; [[_,_]])
\end{code}
%endif

\begin{code}
  data C : Set where
    Fail : C
    Choice : C
  \end{code}
\begin{code}  
  R : C -> Set
  R Fail    = ⊥
  R Choice  = Bool
\end{code}
Here we have chosen to define two possible commands: |Fail| and
|Choice|. The |Fail| constructor corresponds to a non-deterministic
computation that will not return any results; conceptually, the
|Choice| constructor takes two arguments and non-deterministically
chooses between them. To model this, the response used in the
continuation of the free monad, |R Choice|, is a |Bool|, indicating
which argument to choose. We can make this more clear by defining the
following shorthands for non-deterministic computations, |ND|, and
its constructors.
\begin{code}
  ND : Set -> Set
  ND = Free C R

  fail : (Forall(a)) ND a
  fail = Step Fail (\ ())

  choice : (Forall(a)) ND a -> ND a -> ND a
  choice c1 c2 = Step Choice (\ b -> if b then c1 else c2)
\end{code}
Next, we turn our attention to defining a suitable predicate
transformer semantics on Kleisli arrows of the form |(x : a) -> ND (b
x)|. There are two canonical ways to do so:
\begin{code}
  allPT : (Forall (a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> ND (b x) -> Set
  allPT P _ (Pure x)         = P _ x
  allPT P _ (Step Fail k)    = ⊤
  allPT P _ (Step Choice k)  = allPT P _ (k True) ∧ allPT P _ (k False)

  wpAll : (Forall(  a : Set)) (implicit(b : a -> Set)) ((x : a) -> ND (b x)) -> (P : (x : a) -> b x -> Set) -> (a -> Set)
  wpAll f P = wp f (allPT P)

  anyPT : (Forall (a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> ND (b x) -> Set
  anyPT P _ (Pure x)         = P _ x
  anyPT P _ (Step Fail k)    = ⊥
  anyPT P _ (Step Choice k)  = anyPT P _ (k True) ∨ anyPT P _ (k False)

  wpAny : (Forall(  a : Set)) (implicit(b : a -> Set)) ((x : a) -> ND (b x)) -> (P : (x : a) -> b x -> Set) -> (a -> Set)
  wpAny f P = wp f (anyPT P)
\end{code}
These two predicate transformers are dual: |allPT P| holds for a
non-deterministic computation precisely when \emph{all} possible
results satisfy |P|; |anyPt P| holds for a non-deterministic
computation precisely when \emph{some} possible result satisfies |P|.
As we saw for other effects, we can relate both these predicates to the usual `list
handler' for non-determinism.
\begin{code}
  run : (Forall(a)) ND a -> List a
  run (Pure x)         = [ x ]
  run (Step Fail _)    = Nil
  run (Step Choice k)  = run (k True) ++ run (k False)
\end{code}
Finally, we can prove that our predicate transformers are sound with
respect to this semantics. In the case for the |wpAll| function, for
example, this boils down to showing:
%if style == newcode
\begin{code}
  All : {a : Set} -> (a -> Set) -> List a -> Set
  All P Nil = ⊤
  All P (x :: xs) = P x ∧ All P xs

  All++ : {a : Set} (P : a -> Set) (xs ys : List a) ->
    All P xs -> All P ys -> All P (xs ++ ys)
  All++ P Nil ys H1 H2 = H2
  All++ P (x :: xs) ys (Px , H1) H2 = Px , All++ P xs ys H1 H2

  allSoundness : {a : Set} {b : a -> Set} (P : (x : a) -> b x -> Set) (x : a) (nd : ND (b x)) ->
    allPT P x nd -> All (P x) (run nd)
  allSoundness P x (Pure y) H = H , tt
  allSoundness P x (Step Fail _) H = tt
  allSoundness P x (Step Choice k) (H1 , H2) =
    All++ (P x) (run (k True)) (run (k False)) (allSoundness P x (k True) H1) (allSoundness P x (k False) H2)
  \end{code}
%endif
\begin{code}
  wpAllSoundness : (Forall(a)) (implicit(b : a -> Set)) (f : (x : a) -> ND (b x)) ->
    ∀ P x -> wpAll f P x -> All (P x) (run (f x))
\end{code}
%if style == newcode
  \begin{code}
  wpAllSoundness nd P x H = allSoundness P x (nd x) H
  \end{code}
%endif
  The predicate |All P xs| holds whenever the predicate |P|
  holds for all the elements of the list |xs|.
\subsection*{Refinement}  

These two predicate transformer semantics give rise to two different
refinement relations. To characterise both these refinement relations,
we begin by defining the |Elem| relation below, that states that a
given value may be returned by a non-deterministic computation:
\begin{code}
  data Elem (hidden(a : Set)) (x : a) : ND a -> Set where
      Here   : Elem x (Pure x)
      Left   : (Forall(k))  Elem x (k True)   -> Elem x (Step Choice k)
      Right  : (Forall(k))  Elem x (k False)  -> Elem x (Step Choice k)
\end{code}
We can extend this relation to define a `subset' relation on
non-deterministic computations:
\begin{code}    
  _⊆_ : (Forall(a)) ND a -> ND a -> Set
  nd1 ⊆ nd2 = ∀ x -> Elem x nd1 -> Elem x nd2
\end{code}
With these relations in place, we can give the following
characterisation of the refinement relation induced by both the
|wpAll| and |wpAny| predicate transformers:
%if style == newcode
\begin{code}
  _<->_ : {l l' : Level} (a : Set l) (b : Set l') → Set (l ⊔ l')
  a <-> b = Pair (a -> b) (b -> a)
\end{code}
%endif
\begin{code}
  refineAll  : (hidden(a b : Set)) (hidden(x : a)) (f g : a -> ND b) -> (wpAll f  ⊑ wpAll g)  <-> ((x : a) -> g x  ⊆ f x)
  refineAny  : (hidden(a b : Set)) (hidden(x : a)) (f g : a -> ND b) -> (wpAny f  ⊑ wpAny g)  <-> ((x : a) -> f x  ⊆ g x)
\end{code}
%if style == newcode
\begin{code}
  allP : ∀ {a b : Set} {x : a} P (S : ND b) -> allPT P x S <-> (∀ y → Elem y S → P x y)
  Pair.fst (allP P (Pure y)) H y Here = H
  Pair.fst (allP P (Step Choice k)) (H , _) y (Left i) = Pair.fst (allP P (k True)) H y i
  Pair.fst (allP P (Step Choice k)) (_ , H) y (Right i) = Pair.fst (allP P (k False)) H y i
  Pair.snd (allP P (Pure y)) H = H y Here
  Pair.snd (allP P (Step Fail k)) H = tt
  Pair.snd (allP P (Step Choice k)) H = (Pair.snd (allP P (k True)) λ y i → H y (Left i)) , (Pair.snd (allP P (k False)) λ y i → H y (Right i))

  anyP : ∀ {a b : Set} {x : a} P (S : ND b) -> anyPT P x S <-> Sigma b λ y → Elem y S ∧ P x y
  Pair.fst (anyP P (Pure y)) H = y , (Here , H)
  Pair.fst (anyP P (Step Fail k)) ()
  Pair.fst (anyP P (Step Choice k)) (Inl H) with Pair.fst (anyP P (k True)) H
  Pair.fst (anyP P (Step Choice k)) (Inl H) | y , (i , IH) = y , (Left i , IH)
  Pair.fst (anyP P (Step Choice k)) (Inr H) with Pair.fst (anyP P (k False)) H
  Pair.fst (anyP P (Step Choice k)) (Inr H) | y , (i , IH) = y , (Right i , IH)
  Pair.snd (anyP P (Pure y)) (.y , (Here , H)) = H
  Pair.snd (anyP P (Step .Choice k)) (y , (Left i , H)) = Inl (Pair.snd (anyP P (k True)) (y , (i , H)))
  Pair.snd (anyP P (Step .Choice k)) (y , (Right i , H)) = Inr (Pair.snd (anyP P (k False)) (y , (i , H)))

  Pair.fst (refineAll f g) H x y i = Pair.fst (allP (λ _ y' → Elem y' (f x)) (g x)) (H _ x (Pair.snd (allP _ (f x)) (λ _ → id))) y i
  Pair.snd (refineAll f g) r P x H = Pair.snd (allP P (g x)) λ y i -> Pair.fst (allP P (f x)) H y (r x y i)
  Pair.fst (refineAny f g) H x y i with Pair.fst (anyP (λ _ y' → y' == y) (g x)) (H _ x (Pair.snd (anyP _ (f x)) (y , (i , refl))))
  Pair.fst (refineAny f g) H x y i | .y , (i' , refl) = i'
  Pair.snd (refineAny f g) r P x H with Pair.fst (anyP P (f x)) H
  Pair.snd (refineAny f g) r P x H | y , (i , IH) = Pair.snd (anyP P (g x)) (y , ((r x y i) , IH))
\end{code}
%endif
Interestingly, the case for the |wpAny| predicate flips the subset
relation.  Intuitively, if you know that a predicate |P| holds for
\emph{some} element returned by a non-deterministic computation, it is
even `better' to know that |P| holds for a non-deterministic
computation that returns fewer possible results.

\subsection*{Example: non-deterministic deletion}

To illustrate how to reason about such non-deterministic computations,
we will define a function that non-deterministically removes a single
element from an input list, returning both the element removed and the
remaining list. Such a function can typically be used to
non-deterministically inspect the elements of an input list
one-by-one.

Once again, we begin by defining the specification of our function:
\begin{code}
  selectPost : (Forall(a)) List a -> a × List a -> Set
  selectPost xs (y , ys) = Sigma (y ∈ xs) (\ e -> delete xs e == ys)
  
  removeSpec : (Forall(a)) SpecK (List a) (a × List a)
  removeSpec = [[ K ⊤ , selectPost ]]
\end{code}
The precondition holds trivially; the postcondition consists of two
parts, paired together using a |Sigma|-type. The first component of
the postcondition states that the element returned, |y|, is an element
of the input list |xs|. Here we use the |_∈_| relation characterising
the elements of a list from the standard library. The second component
of the postcondition states that removing this element from the input
list produces the output list. Here we use an auxiliary function,
|delete|, that removes an existing element from a list:
\begin{spec}
    delete : (Forall(a)) (implicit(x : a)) (xs : List a) -> x ∈ xs -> List a  
\end{spec}
The definition recurses over the proof of |x ∈ xs|, reconstructing the
output list along the way.

With the specification in place, we can define the following function
that draws an element from its input list non-deterministically.
\begin{code}  
  remove : (Forall(a)) List a -> ND (a × List a)
  remove Nil        = fail
  remove (x :: xs)  = choice  (return (x , xs)) (map (retain x) (remove xs))
      where
      retain : (Forall(a)) a -> a × List a -> a × List a
      retain x (y , ys) = (y , (x :: ys))
\end{code}
Verifying the correctness of this function amounts to proving the following lemma:
\begin{code}  
  removeCorrect : (Forall(a)) wpSpec (hidden(a = List a)) (hidden(const (a × List a))) removeSpec ⊑ wpAll remove
\end{code}
%if style == newcode
\begin{code}
  removeCorrect P Nil (tt , snd) = tt
  removeCorrect P (x :: xs) (tt , snd) =
    snd (x , xs) (∈Head , refl) ,
    mapPT P (x :: xs) xs (remove xs) _
      (removeCorrect _ xs (tt , (λ {(x' , xs') (i , H) → snd (x' , (x :: xs')) (∈Tail i , cong (x ::_) H)})))
    where
    mapPT : ∀ {a b c : Set} P (x x' : a) (S : ND b) (f : b → c) → allPT (λ _ y → P x (f y)) x' S → allPT P x (map f S)
    mapPT P x x' (Pure y) f H = H
    mapPT P x x' (Step Fail k) f H = H
    mapPT P x x' (Step Choice k) f (fst , snd) = mapPT P x x' (k True) f fst , mapPT P x x' (k False) f snd
\end{code}
%endif
Note that this correctness property merely states that all the pairs
returned by |remove| satisfy the desired postcondition. It does not
require that all possible decompositions of the input list also occur
as possible results of the |remove| function. There is a trivial proof
that the |fail| computation also satisfies this specification:
\begin{code}
  trivialCorrect : (Forall(a)) wpSpec (hidden(a = List a)) (hidden(const (a × List a))) removeSpec ⊑ wpAll (const fail)  
\end{code}
%if style == newcode
\begin{code}
  trivialCorrect = \ P xs H → tt
\end{code}
%endif
In other words, the lemma |removeCorrect| guarantees the
\emph{soundness}, but not the \emph{completeness} of our
non-deterministic computation.

We can address this by proving an additional lemma, stating that the
|remove| function returns every possible list decomposition:
\begin{code}
  completeness : (Forall(a)) (y : a) (xs ys : List a) -> selectPost xs (y , ys) -> Elem (y , ys) (remove xs)
\end{code}
%if style == newcode
\begin{code}
  completeness y (y :: _) ys (∈Head , refl) = Left Here
  completeness y (x :: xs) .(x :: delete xs fst) (∈Tail fst , refl) = Right (inMap _ (remove xs) _ (completeness y _ _ (fst , refl)))
    where
    inMap : ∀ {a b : Set} (x : a) S (f : a → b) → Elem x S → Elem (f x) (map f S)
    inMap x (Pure x) f Here = Here
    inMap x (Step Choice k) f (Left i) = Left (inMap x (k True) f i)
    inMap x (Step Choice k) f (Right i) = Right (inMap x (k False) f i)
\end{code}
%endif
The proof proceeds by induction on the first component of the
postcondition, |y ∈ xs|.

\section{General recursion}
\label{sec:recursion}

%if style == newcode
\begin{code}
module Recursion where
  open Free
  open import Data.Nat public
    using
      (_+_; _>_; _*_
      )
    renaming
      ( ℕ to Nat
      ; zero to Zero
      ; suc to Succ
      ; _∸_ to _-_
      )
  open NaturalLemmas
  open Maybe hiding (soundness)
\end{code}
%endif


Giving a constructive semantics for \emph{general recursion} may seem
quite difficult at first glance. There are a variety of techniques
that account for general recursion in type
theory~\cite{bove_krauss_sozeau_2016}. Inspired
by~\citet{mcbride2015turing}, however, we show how the call graph of a
recursive functions can be described as a free monad, to which we can
in turn assign predicate transformer semantics.

Suppose we wish to define a recursive function of type |(i : I) -> O
i|, for some input type |I : Set| and output type |O : I -> Set|. If
the recursion is structural, we typically do so by induction on
the argument of type |I|. If it is not, we may still want to describe the intended function
and its behaviour---deferring any proof of termination for the
moment. We can describe such functions as follows:
\begin{code}
  _~~>_ : (I : Set) (O : I → Set) → Set
  I ~~> O = (i : I) → Free I O (O i)
\end{code}
Once again, we have a Kleisli arrow on the |Free| monad. The choice of
`commands' and `responses', however, are somewhat puzzling at
first. The intuition is that the `effect' we are allowed to use
amounts to consulting an oracle, that given an input |j : I| returns
the corresponding output in |O j|. A Kleisli arrow of the form |I ~~>
O| takes an input |i : I| and may make any number of recursive calls,
before returning a value in |O i|.

As before, we define a smart constructor to make such calls:
\begin{code}
  call : (Forall (I O)) (i : I) → Free I O (O i)
  call x = Step x Pure
\end{code}
Note that we do \emph{not} define recursive functions---but rather
define an explicit representation of the call graph of the function
we wish to define. This gives a finite representation of the recursive
structure of our program.

To illustrate this point, we can define McCarthy's 91-function. The
recursive structure of this function is notoriously difficult to
express in a total language such as Agda:
\begin{code}
  f91 : Nat ~~> K Nat
  f91 i with 100 lt i
  f91 i | yes  _  = return (i - 10)
  f91 i | no   _  = call (i + 11) >>= call
\end{code}
This definition is not recursive, but merely makes the recursive
structure of the function body, |f91 (f91 (i + 11))|, explicit. The
first |call| corresponds to the inner application |f91 (i + 11)|; the
result of this is fed to the second |call|, corresponding to the
outer application.

How can we reason about such functions? As is customary in the
literature on predicate transformer semantics, we distinguish between
\emph{total correctness} and \emph{partial correctness}. For the
moment, we will only concern ourselves with proving \emph{partial
  correctness} of our programs: provided a program terminates, it
should produce the right result.

To prove partial correctness of the |f91| function, we define the
following specification:
\begin{code}
  f91Post : Nat → Nat → Set
  f91Post i o with 100 lt i
  f91Post i o | yes _  = o == i - 10
  f91Post i o | no _   = o == 91

  f91Spec : SpecK Nat Nat
  f91Spec = [[ K ⊤ , f91Post ]]
\end{code}

Although we cannot directly run `recursive' functions defined in this
style, such as the |f91| function, we can reason about their
correctness. To do so, we would like to show that a Kleisli arrow |I
~~> O| satisfies some specification of type |Spec I O|. To achieve
this, we begin by defining an auxiliary function, |invariant|, that
asserts that a given call-graph |Free I O (O i)| respects the
invariant arising from a given specification:
\begin{code}
  invariant : (Forall(I)) (implicit(O : I -> Set)) (i : I) -> Spec I O  -> Free I O (O i) -> Set
  invariant i [[ pre , post ]] (Pure x)    =  pre i -> post i x
  invariant i [[ pre , post ]] (Step j k)  =  (pre i -> pre j)
                                              ∧ ∀ o -> post j o -> invariant i [[ pre , post ]] (k o)
\end{code}
If there are no recursive calls, the postcondition must hold, provided
the precondition does. If there is a recursive call on the argument |j
: I|, the precondition must hold for |j|, assuming it holds initially
for |i|. Furthermore, for any for result |o : O j| satisfying the
postcondition, the remaining continuation |k o| must continue to
satisfy the desired specification.

Using this definition, we can now formulate a predicate transformer
semantics for Kleisli arrows of the form |I ~~> O|.
\begin{code}
  wpRec : (Forall(I)) (implicit(O : I -> Set)) Spec I O -> (f : I ~~> O) -> (P : (i : I) -> O i -> Set) -> (I -> Set)
  wpRec spec f P i = wpSpec spec P i ∧ invariant i spec (f i) 
\end{code}
In contrast to the semantics we have seen so far, the |wpRec| function
requires a \emph{specification} as argument to determine a semantics
of a \emph{computation}. This is analogous to how imperative programs
require an explicit loop invariant: assigning semantics to recursive
functions requires an explicit specification. The predicate
transformer semantics |wpRec| states that this specification is indeed
satisfied if any recursive call respects the corresponding invariant.

Using the |wpRec| function, we can formulate the partial correctness
of the |f91| function as follows.
\begin{code}
  f91Partial-correctness : wpSpec f91Spec ⊑ wpRec f91Spec f91
\end{code}
%if style == newcode
\begin{code}
  f91Partial-correctness P i with 100 lt i
  f91Partial-correctness P i | yes p with 100 lt i
  f91Partial-correctness P i | yes p | yes _ = \ H → (tt , (\ x eq → Pair.snd H _ eq)) , (\ x → refl)
  f91Partial-correctness P i | yes p | no ¬p = magic (¬p p)
  f91Partial-correctness P i | no ¬p = \ x → (tt , (\ x₁ x₂ → Pair.snd x x₁ x₂)) ,
                                              ((\ _ → tt) , (\ o x₁ → (\ x₂ → tt) ,
                                              (\ o₁ x₂ x₃ → lemma i o _ ¬p x₁ x₂)))
    where
    open Data.Nat
    open import Data.Nat.Properties

    100-≮-91 : (i : Nat) → ¬ (i + 10 ≤ i)
    100-≮-91 Zero ()
    100-≮-91 (Succ i) (s≤s pf) = 100-≮-91 i pf

    plus-minus : ∀ b c → (b + c) - c == b
    plus-minus b c = trans (+-∸-assoc b (NaturalLemmas.≤-refl {c})) (trans (cong (b +_) (n∸n≡0 c)) (sym (plus-zero b)))
    plus-plus-minus : ∀ i → i + 11 - 10 ≡ Succ i
    plus-plus-minus i = plus-minus (Succ i) 11
    between : ∀ a b → ¬ (a < b) → a < Succ b → a ≡ b
    between Zero Zero ¬lt ltSucc = refl
    between Zero (Succ b) ¬lt ltSucc = magic (¬lt (s≤s z≤n))
    between (Succ a) Zero ¬lt (s≤s ())
    between (Succ a) (Succ b) ¬lt (s≤s ltSucc) = cong Succ (between a b (¬lt ∘ s≤s) ltSucc)

    lemma : ∀ i o o' → ¬ (100 < i) →
      f91Post (i + 11) o → f91Post o o' → f91Post i o'
    lemma i o o' i≤100 oPost o'Post with 100 lt i
    ... | yes p = magic (i≤100 p)
    ... | no ¬p with 100 lt o
    lemma i o .(o - 10) i≤100 oPost refl | no ¬p | yes p with 100 lt (i + 11)
    lemma i .(i + 11 - 10) .(i + 11 - 10 - 10) i≤100 refl refl | no ¬p | yes p | yes p₁ with between 100 i i≤100 (subst (\ i' → 100 < i') (plus-plus-minus i) p)
    lemma .100 .101 .91 i≤100 refl refl | no ¬p | yes p | yes p₁ | refl = refl
    lemma i .91 .81 i≤100 refl refl | no ¬p | yes p | no ¬p₁ = magic (100-≮-91 91 p)
    lemma i o o' i≤100 oPost o'Post | no ¬p | no ¬p₁ = o'Post
\end{code}
%endif
The proof mimics the definition of the |f91| function. After comparing
the input |i| to 100, the base case follows immediately. The recursive
case, however, requires various auxiliary lemmas stating properties of subtraction.

What do we know about the soundness of |wpRec|? The semantics compute
some predicate on the input |I|, but we would like to have some
guarantee that this predicate is meaningful. Unfortunately, there is
no way to run arbitrary recursive functions without compromising the
soundness of Agda's type system. There are, however, a variety of
techniques to guarantee the termination of recursive functions such
as: bounding the number of iterations, generating a coinductive trace,
adding a coinductive fixpoint operator~\cite{capretta}, proving the
recursive calls are well-founded, or performing induction on an
auxiliary data structure~\cite{bove-capretta}.

We can prove a simple soundness result in terms of the `petrol-driven
semantics' that runs a computation for a fixed number of steps.
\begin{code}
  petrol : (Forall(I O a)) (f : I ~~> O) -> Free I O a -> Nat -> Partial a
  petrol f (Pure x)    n         = return x
  petrol f (Step _ _)  Zero      = abort
  petrol f (Step c k)  (Succ n)  = petrol f (f c >>= k) n 
\end{code}
The last case is the only interesting one: it unfolds the function |f|
once, decrementing the number of steps remaining. We would like to use
this semantics, to formulate and prove the soundness of |wpRec|.
There is one problem: the |petrol| function may fail to return a
result and |abort|. Fortunately, we can define yet another predicate
transformer semantics for partial computations:
\begin{code}
  mayPT : (Forall(a)) (a -> Set) -> (Partial a -> Set)
  mayPT P (Pure x)        = P x
  mayPT P (Step Abort _)  = ⊤
\end{code}
With these definitions in place, we can finally formulate and prove a
soundness result regarding our |wpRec| semantics:
\begin{code}
  soundness : (Forall (I O)) (f : I ~~> O) (spec : Spec I O) (P : (i : I) -> O i -> Set) ->
    (∀ i -> wpRec spec f P i) -> ∀ n i → mayPT (P i) (petrol f (f i) n)
\end{code}
This lemma guarantees that---under the assumption that 
|wpRec| holds for all inputs---whenever the petrol-driven semantics manage
to produce a result, this result is guaranteed to satisfy the predicate |P|.
We could show similar soundness results for the other handlers that
\citet{mcbride2015turing} proposes for general recursion; this soundness result,
however, provides at least some evidence
that the predicate transformer semantics for recursion, |wpRec|, is correct.
  
%if style == newcode
\begin{code}
  soundness f spec P wpH n i = soundness' f spec P (f i) n wpH (wpH i)
    where
    invariant-compositionality : ∀ {I} {O : I → Set} {i i'} spec
      (S : Free I O (O i)) (k : (O i) -> Free I O (O i')) ->
      invariant i spec S -> Spec.pre spec i -> (∀ o → Spec.post spec i o → invariant i' spec (k o)) ->
      invariant i' spec (S >>= k)
    invariant-compositionality spec (Pure x) k SH preH kH = kH x (SH preH)
    invariant-compositionality spec (Step c k') k (fst , snd) preH kH = (\ _ → fst preH) , \ o postH → invariant-compositionality spec (k' o) k (snd o postH) preH kH
    soundness' : ∀ {I} {O : I → Set} {i}
      (f : (i : I) → Free I O (O i)) (spec : Spec I O) (P : (i : I) -> O i → Set)
      (S : Free I O (O i)) (n : Nat) ->
      (∀ i -> wpRec spec f P i) ->
      wpSpec spec P i ∧ invariant i spec S ->
      mayPT (P i) (petrol f S n)
    soundness' f spec P (Pure x) n wpH ((preH , postH) , invH) = postH x (invH preH)
    soundness' f spec P (Step c k) Zero wpH H = tt
    soundness' f spec P (Step c k) (Succ n) wpH (specH , (preH , postH)) = soundness' f spec P (f c >>= k) n wpH (specH , invariant-compositionality spec (f c) k (Pair.snd (wpH c)) (preH (Pair.fst specH)) postH)
\end{code}
%endif

\section{Stepwise refinement}
\label{sec:stepwise-refinement}

%if style == newcode
\begin{code}
module Mix (C : Set) (R : C -> Set) (ptalgebra : (c : C) -> (R c -> Set) -> Set) where
  open Free hiding (_>>=_)
  open Maybe using (SpecK; [[_,_]]; Spec; wpSpec)
\end{code}
%endif

In the examples we have seen so far, we have related a \emph{complete}
program to its specification. Most work on the refinement calculus,
however, allows programs and specifications to mix freely, thereby
enabling the step-by-step refinement of a specification into an
executable program. How can we support this style of program
calculation using the predicate transformer semantics we have seen so
far?

Until now we have concerned ourselves with free monads of the form |Free
C R a| and the Kleisli arrows that produce them. Such free monads give
a structured representation of a series of interactions, (potentially)
ending in a value of type |a|. By varying this
information stored in the leaves of the free monad, we can mix
unfinished specifications and program fragments.

To this end, we begin by defining the following shorthand for
specifications on values, rather than the specifications on (Kleisli)
arrows we have considered previously:
\begin{code}
  SpecVal : Set -> SetOne
  SpecVal a = SpecK ⊤ a
 \end{code}
These specifications consist of a
precondition of type |Set| and a predicate |a -> Set|.
Next, we can define the datatype |I a|, corresponding to either a
specification on |a| or a value of type |a|.
\begin{code}
  data I (a : Set) : SetOne where
    Done  : a -> I a
    Hole  : SpecVal a -> I a
\end{code}
Here we use the |Hole| constructor to store
a specification, corresponding to some unfinished part of the program being
calculated. We can assign a predicate transformer semantics to values
of type |I a| easily enough, reusing our previous |wpSpec| function:
\begin{code}
  ptI : (Forall(a)) I a -> (a -> Set) -> Set
  ptI (Done x)     P  = P x
  ptI (Hole spec)  P  = wpSpec spec (hiddenConst(P)) tt
\end{code}
Furthermore, given the commands |C| and responses |R| that determine the
operations of a free monad, we can define the following datatype for
partially finished programs:
\begin{code}  
  M : Set -> SetOne
  M a = Free C R (I a)
\end{code}
The type |M a| describes computations that \emph{mix} code
and specifications. A value of type |M a| consists of a number of
operations, given by the |Step| constructor of the |Free C R| type constructor; in
contrast to free monads we have seen so far, however, the leaves
contain either values of type |a| or specifications, representing
unfinished parts of the program's derivation.

In what follows, we will be careful to distinguish \emph{executable
  code}---that is programs without specification fragments---from
programs, that may still contain specifications. The following
predicate characterises the executable fragment of |M a|:
\begin{code}
  isExecutable : (Forall(a)) M a -> Set
  isExecutable (Pure (Done _))  = ⊤
  isExecutable (Pure (Hole _))  = ⊥
  isExecutable (Step c k)       = ∀ r -> isExecutable (k r)
\end{code}

Although we have defined the syntactic structure of our mixed
computations, |M a|, we have not yet given their semantics. We can reuse
the notion of weakest precondition on |I| to define a notion of
weakest precondition for the computations in |M|. To do so, however,
we need to assume that we have some weakest precondition semantics for
Kleisli morphisms:
%if style == newcode
\begin{code}
  pt : (Forall(l)) (implicit(a : Set l)) Free C R a -> (a -> Set) -> Set
  pt (Pure x) P   = P x
  pt (Step c x) P = ptalgebra c (\r -> pt (x r) P)
\end{code}
%endif
\begin{code}
  wpCR : (Forall(l l')) (implicit(a : Set l)) (implicit(b : a -> Set l')) ((x : a) -> Free C R (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
\end{code}
%if style == newcode
\begin{code}
  wpCR f P x = pt (f x) (P x)
\end{code}
%endif
We have seen many examples of such semantics in the previous sections
for specific choices of |C| and |R|. We can now assign semantics to
`unfinished' programs as follows:
\begin{code}
  wpM : (implicit(a : Set)) (implicit(b : a -> Set)) ((x : a) -> M (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpM f P x = wpCR f (\ x ix -> ptI ix (P x)) x
\end{code}
The crucial step here is to transform the argument predicate |P| to
work on specifications or values of type |I a|, using the |ptI|
function defined above.

\subsection*{Defining derivations}
\label{case-study}
%if style == newcode
\begin{code}
module StateExample where
  open Free hiding (_>>=_)
  open Maybe using (Spec; SpecK; [[_,_]]; wpSpec)
  open State Nat
\end{code}
%endif
The |wpM| function assigns a predicate transformer semantics to
unfinished programs, where the leaves of a free monad may consist of
values or specifications. We can use this semantics to derive a
program from its specification in series of refinement steps. A
\emph{program derivation} consists of a series of refinement steps
from some initial specification:
\begin{center}
\begin{spec}
  wpSpec spec ⊑ wpM i1 ⊑ wpM i2 ⊑ ... ⊑ wpCR c
\end{spec}
\end{center}
Here the intermediate steps (|i1|, |i2|, and so forth) may mix
specifications and effectful computations; the final program, |c|, must be
executable.



%if style == newcode
\begin{code}
  --  We have to redo the Mix section since our specifications incorporate the state
  SpecVal : ∀ {l} → Set → Set (suc l)
  SpecVal = SpecK Nat
  data I {l : Level} (a : Set) : Set (suc l) where
    Done  : a -> I a
    Hole  : SpecVal {l} (a × Nat) -> I a
  M : {l : Level} -> Set -> Set (suc l)
  M a = State (I a)
  ptI : forall {l a } ->  I a -> (a × Nat -> Set l) -> Nat -> Set l
  ptI (Done x)     P t  = P (x , t)
  ptI (Hole spec)  P t  = wpSpec spec (\_ -> P) t
  wpM : forall {l l'} { a : Set l} {b : Set } -> (a -> M b) -> (a × Nat -> b × Nat -> Set l') -> (a × Nat -> Set l')
  wpM f P = wpState f (\ i o -> ptI (Pair.fst o) (P i) (Pair.snd o))
  ptM : {a : Set} -> M a -> (Nat -> a × Nat -> Set) -> (Nat -> Set)
  ptM S post t = wpM (λ _ → S) (λ _ → (post t)) (⊤ , t)
  liftM : ∀ {l : Level} {a} → M {l} a → M {suc l} a
  liftM (Pure (Done x)) = Pure (Done x)
  liftM (Pure (Hole [[ pre , post ]])) = Pure (Hole [[ (λ x → Lift _ (pre x)) , (λ i o → Lift _ (post i o)) ]])
  liftM (Step c k) = Step c λ x → liftM (k x)
  _>>=_ : forall {l a b } ->  (M {l} a) -> (a -> M {l} b) -> M {suc l} b
  Pure (Done x) >>= f     = liftM (f x) 
  Pure (Hole [[ pre , post ]]) >>= f  =
    Pure (Hole [[ (λ n -> Lift _ (pre n)) ,
      (\i ynat -> ∀ x -> post i (x , i) → ∀ P -> wpM f P (x , i) -> P (x , i) ynat
      ) ]] )
  (Step c k) >>= f        = Step c (\ r →  k r >>= f)
  _>=>_ : forall {l : Level} {a b c : Set} -> (a -> M {l} b) -> (b -> M {l} c) -> a -> M {suc l} c
  (f >=> g) x = f x >>= g

  specV : {a : Set} -> SpecVal {zero} (a × Nat) -> M a
  specV spec = Pure (Hole spec)
\end{code}
%endif


Before calculating an example program in this style, we will develop a handful
of auxiliary definitions, specialised to the stateful computations
described in Section~\ref{sec:state}; it should be straightforward
to adapt the definitions to work for other effects.
In what should be a familiar pattern, we begin by defining a handful
of smart constructors:
%if style == poly
%format get' = get
%format put' = put
%format specF = spec
%endif
\begin{code}
  done   : (Forall (a)) a -> M (hidden(zero)) a
  get'   : M Nat
  put'   : Nat -> M ⊤
\end{code}
%if style == newcode
\begin{code}
  done x = Pure (Done x)
  get' = Step Get done
  put' t = Step (Put t) done

\end{code}
%endif

Note that these smart constructors now produce computations in |M|,
mixing effects and specifications, rather than the free monad,
|State|, we saw previously.  We can define the following
postconditions characterising |get| and |put|:
\begin{code}
  getPost : Nat -> Nat × Nat → Set
  getPost t (x , t') = (t == x) ∧ (t == t')
  putPost : Nat -> Nat → ⊤ × Nat → Set
  putPost t _ (_ , t') = t == t'
\end{code}
As you would expect, these postconditions state that |get| returns the current state but does not
modify it; the |put| command overwrites the current state. We can
prove that |get| and |put| commands satisfy these postconditions using
our |wpM| semantics:
\begin{spec}
  getCorrect  : forall pre     ->  wpSpec [[ pre , (\ i o -> pre i ∧ getPost i o) ]]    ⊑ ptM get'
  putCorrect  : forall pre x   ->  wpSpec [[ pre , (\ i o -> pre i ∧ putPost x i o) ]]  ⊑ ptM (put' x)
\end{spec}
%%In the spec above, this should really be ptM...
%if style == newcode
% \begin{code}
%   getCorrect _ P t (fst , snd) = snd (t , t) (fst , (refl , refl))
%   putCorrect _ t P _ (fst , snd) = snd (tt , t) (fst , refl)
% \end{code}
%endif
While we will not use these properties in the remainder of our
calculation directly, they form an important sanity check, guaranteeing that
the specifications we have chosen for |get| and |put| are correct.

To derive a program from its specification, we will perform a series
of refinement steps. While we could use the transitivity of the refinement relation
to chain together various intermediate programs explicitly, we take a slightly
different approach.
Each refinement step is allowed to introduce a single new command of type |C|, thereby
changing the remaining refinement problem. We can try to make this manifest
in the following (incomplete) datatype:
\begin{spec}
  data Derivation (hidden(b : Set)) (spec : SpecVal b) : SetOne where
    Done  : (x : b) ->  wpSpec spec ⊑ ptM (done x)       -> Derivation spec
    Step  : (c : C) ->  (∀ (r : R c) -> Derivation ...)  -> Derivation spec
\end{spec}
A value of type |Derivation spec| describes a series of refinement
steps, yielding a value satisfying the desired specification. In the
base case, the derivation is done and returns a value |x : b| that
satisfies the desired specification; otherwise, we perform the command |c| and continue
the remainder of the program derivation---
but how does introducing the command |c| modify the remaining
specification problem? To answer this question, we need to make
explicit what the effect of each command is on the current
specification goal. Fortunately, the specifications of |get| and |put| defined
previously will allow us to do just that.

We would like to define a function that, given a new command |c|,
computes the specification of the remaining continuation:
\begin{spec}
  step : (Forall(b)) (c : C) (spec : SpecVal (b × Nat)) -> SpecK (R c × Nat) (b × Nat)  
\end{spec}
To achieve this, we define a pair of predicate transformers that use
the postcondition associated with the command |c| to modify the
current specification. The first such transformer computes a new
precondition of type |b -> Set|, given the current specification's
precondition |P : a -> Set|.
\begin{code}
  _tril_ : (implicit(a b : Set)) (Q : a → b → Set) (P : a → Set) → b → Set
  _tril_ (hidden(a)) Q P = \ y -> Sigma a (\ x → P x ∧ Q x y)
\end{code}
This limited form of relational composition requires an intermediate
result, |x : a|, and proofs that |x| satisfies both |P| and |Q|.  Our
second transformer computes a new postcondition of the remaining
specification:
\begin{code}
  _trir_ : (implicit(a b c : Set)) (Q : a → b → Set) -> (SpecK a c) → b → c → Set
  _trir_ Q [[ pre , post ]] = \ y z -> ∀ x → pre x ∧ Q x y → post x z
\end{code}
The new postcondition requires that the original postcondition |post|
holds, whenever the postcondition |Q|---associated with the new
command we are introducing---and initial precondition |pre| hold.

Using these definitions, we can complete the definition of the
|step| function:
\begin{code}
  step : (Forall(b)) (c : C) (spec : SpecVal (hidden(zero)) (b × Nat)) -> SpecK (hidden(zero)) (R c × Nat) (b × Nat)
  step Get      [[ pre , post ]] = [[ getPost tril pre , getPost trir [[ pre , post ]] ]]
  step (Put x)  [[ pre , post ]] = [[ (putPost x) tril pre , (putPost x) trir [[ pre , post ]] ]]
\end{code}
The |step| function uses the above operators, together with the
postconditions associated with |get| and |put|, to compute
a new specification for the remaining derivation.

Before completing the definition of derivations, there is one last
issue to address. Using the |step| function, we can compute a new
specification for the remaining continuation after a |put| or |get|
command. Our derivations, however, only contain specifications of
\emph{values}---represented by |SpecVal|---rather than the specification of a
function, represented by |Spec|. Fortunately, we can easily convert between the two:
\begin{code}
  intros : (Forall(a b)) SpecK (hidden(zero)) (a × Nat) (b × Nat) -> a -> SpecVal (b × Nat)
\end{code}
The |intros| function (partially) applies the precondition and
postcondition to the argument of type |a|; the name is suggestive of
the corresponding Coq tactic.
%if style == newcode
\begin{code}
  intros [[ pre , post ]] x = [[ (\ t -> pre (x , t)) , (\ t → post (x , t)) ]]
\end{code}
%endif
Finally, we can complete the definition of derivations using the
|step| and |intros| functions.
\begin{code}
  data Derivation (hidden(b)) (spec : SpecVal (b × Nat)) : SetOne where
    Done : (x : b) -> wpSpec spec ⊑ ptM (done x) -> Derivation spec
    Step : (c : C) -> (∀ (r : R c) -> Derivation (intros (step c spec) r)) -> Derivation spec
\end{code}
The interesting case is in the continuation of the |Step|
constructor. For each possible response |r : R c|, we need to provide
a derivation of the remaining specification. Note that we have
specialized this type to work over stateful computations by requiring a
specification on the result and output state.
  
It is no coincidence that the structure of our derivations mimics that
of the computations described by our |Free| datatype.  One advantage
of giving a manifest representation of such derivations is that we
can easily extract executable code from a given derivation:
\begin{code}
  extract : (Forall(b)) (spec : SpecVal (b × Nat)) -> Derivation spec -> State b
  extract _ (Done x _)  = Pure x
  extract _ (Step c k)  = Step c (\ r -> extract _ (k r))
\end{code}
Furthermore, we can prove that any extracted program does indeed satisfy its
intended specification.

%if style == newcode
\begin{code}

  DerivationFun : {a b : Set} (spec : SpecK (a × Nat) (b × Nat)) -> SetOne
  DerivationFun {a} {b} spec = (x : a) -> Derivation (intros spec x)

  stepMonotone : {a : Set} (c : C) (r : R c) {spec spec' : SpecVal (a × Nat)} ->
    wpSpec spec ⊑ wpSpec spec' ->
    wpSpec (intros (step c spec) r) ⊑ wpSpec (intros (step c spec') r)
  stepMonotone {a} Get r {spec} {spec'} H P .r ((.r , (fst₁ , (refl , refl))) , snd) = (r , (Pair.fst (H (\ _ _ → ⊤) r (fst₁ , (\ x _ → tt))) , (refl , refl))) , \ x x₁ → snd x (postLemma r x x₁)
    where
    postLemma : ∀ r
      (x : Pair a Nat) →
      (∀ x₁ →
      Pair (Spec.pre spec' x₁) (Pair (x₁ ≡ r) (x₁ ≡ r)) →
      Spec.post spec' x₁ x) →
      ∀ x₁ →
      Pair (Spec.pre spec x₁) (Pair (x₁ ≡ r) (x₁ ≡ r)) →
      Spec.post spec x₁ x
    postLemma r x x₂ .r (fst , (refl , refl)) = Pair.snd (H (Spec.post spec) r (fst , (\ x₃ z → z))) x (x₂ r ((Pair.fst (H (\ _ _ → ⊤) r (fst , (\ x₃ _ → tt)))) , (refl , refl)))
  stepMonotone {a} (Put t) r {spec} {spec'} H P .t ((fst , (fst₁ , refl)) , snd) = (fst , (Pair.fst (H (\ _ _ → ⊤) fst (fst₁ , (\ x _ → tt))) , refl)) , \ x x₁ → snd x (postLemma t x x₁)
    where
      postLemma : ∀ (t : Nat)
        (x : Pair a Nat) →
        (∀ x₁ → Pair (Spec.pre spec' x₁) (t ≡ t) → Spec.post spec' x₁ x) →
        ∀ x₁ →
        Pair (Spec.pre spec x₁) (t ≡ t) → Spec.post spec x₁ x
      postLemma t x x₁ x₂ (fst , refl) = Pair.snd (H (Spec.post spec) x₂ (fst , (\ x₃ z → z))) x (x₁ x₂ ((Pair.fst (H (\ _ _ → ⊤) x₂ (fst , (\ x₃ _ → tt)))) , refl))

  open import Data.Nat
  open import Data.Nat.Properties
  open NaturalLemmas hiding (≤-refl ; ≤-trans)

  data All {a : Set} (P : a → Set) : List a → Set where
    AllNil : All P Nil
    AllCons : ∀ {x xs} → P x → All P xs → All P (x :: xs)
  unAllCons : ∀ {a P x} {xs : List a} →
    All P (x :: xs) → All P xs
  unAllCons (AllCons x₁ x₂) = x₂
\end{code}
%endif

\subsection*{Case study: calculating the maximum}
\label{sec:maximum}

With our definition of derivations in place, we can finally turn our
attention to an example calculation. In this section, we will derive a
simple program that computes the greatest element of a non-empty
list. Although there is a simple, purely functional implementation, we
choose to derive a stateful version that stores the greatest element
encountered so far. Once again, we stress that our aim is \emph{not}
to perform complex program calculations, but rather to illustrate the
definitions we have given in the previous pages.

We begin by defining the specification of our desired function:
\begin{code}
  maxPre : List Nat × Nat → Set
  maxPre (xs , i) = (i == 0) ∧ (¬ (xs == Nil))
  maxPost : List Nat × Nat → Nat × Nat → Set
  maxPost (xs , i) (o , _) = All (o ≥_) xs ∧ (o ∈ xs)
  maxSpec = [[ maxPre , maxPost ]]
\end{code}
Given an initial state |0| and non-empty list |xs|, our |max| function
should find a number |o| that is both greater than or equal to all the
elements of |xs| and also occurs in |xs|.

To calculate a suitable implementation amounts to proving that
|Derivation maxSpec| is inhabited. A direct proof quickly fails, as
the statement is not general enough to reuse our induction
hypothesis. We can prove, however, the following lemma that allows us
to modify the target of our derivation:
\begin{code}
  refineDerivation : (Forall(a : Set)) (implicit(spec spec' : SpecVal (a × Nat))) wpSpec spec ⊑ wpSpec spec' -> Derivation spec' -> Derivation spec
\end{code}
%if style == newcode
\begin{code}
  refineDerivation H (Done x Hx) = Done x (⊑-trans H Hx)
  refineDerivation H (Step c d) = Step c \ r → refineDerivation (stepMonotone c r H) (d r)
\end{code}
%endif
The proof recurses over the derivation and relies on the monotonicity of our predicate transformers.
In particular, we can use this lemma, together with the |weakenPre|
and |strengthenPost| lemmas from Section~\ref{sec:state}, to generalise
our specification and perform the bookkeeping necessary on the
intermediate specifications we encounter during derivation.

We can use the |refineDerivation| lemma to show that the following
formulation of the desired postcondition also suffices:
\begin{code}
  maxPost' : List Nat × Nat → Nat × Nat → Set  
  maxPost' (xs , i) (o , _) = All (o ≥_) (i :: xs) × (o ∈ (i :: xs))
\end{code}
%if style == newcode
\begin{code}
  maxProof : ∀ (xs : List Nat) ->
    wpSpec (intros [[ maxPre , maxPost ]] xs) ⊑
    wpSpec (intros [[ K ⊤ , maxPost' ]] xs)
  maxProof xs P .0 ((refl , Hnil) , snd) = tt , \ o H → snd o (unAllCons (Pair.fst H) , lemma xs Hnil (Pair.fst o) H)
    where
    lemma : ∀ xs → ¬ (xs == Nil) →
      ∀ w → Pair (All (\ n → n ≤ w) (0 :: xs)) (w ∈ (0 :: xs)) → w ∈ xs
    lemma Nil Hnil w H = magic (Hnil refl)
    lemma (.0 :: xs) _ .0 (AllCons x₂ (AllCons z≤n fst) , ∈Head) = ∈Head
    lemma (x :: xs) _ w (_ , ∈Tail snd) = snd

  max'ProofNil : ∀ i →
    wpSpec (intros (step Get (intros [[ K ⊤ , maxPost' ]] Nil)) i) ⊑ ptM (done i)
  max'ProofNil i P .i ((.i , (fst₁ , (refl , refl))) , snd) = snd (i , i) (lemma i)
    where
    lemma : ∀ i x →
      Pair ⊤ (Pair (x ≡ i) (x ≡ i)) →
      Pair (All (\ n → n ≤ i) (x :: Nil)) (i ∈ (x :: Nil))
    lemma i .i (fst , (refl , refl)) = (AllCons ≤-refl AllNil) , ∈Head

  max'Proof1 : ∀ x xs i →
    Succ x ≤ i →
    ∀ (P : Nat → Nat × Nat → Set) x₁ →
    Pair (Sigma ℕ (\ x₂ → Pair ⊤ (Pair (x₂ ≡ i) (x₂ ≡ x₁))))
    (∀ x₂ →
    (∀ x₃ →
    Pair ⊤ (Pair (x₃ ≡ i) (x₃ ≡ x₁)) →
    Pair (All (\ n → n ≤ Pair.fst x₂) (x₃ :: x :: xs))
    (Pair.fst x₂ ∈ (x₃ :: x :: xs))) →
    P x₁ x₂) →
    Pair ⊤
    (∀ x₂ →
    Pair (All (\ n → n ≤ Pair.fst x₂) (x₁ :: xs))
    (Pair.fst x₂ ∈ (x₁ :: xs)) →
    P x₁ x₂)
  max'Proof1 x xs i x<i P .i ((.i , (_ , (refl , refl))) , snd) = tt , \ x₂ x₁ → snd x₂ (lemma x₂ x₁)
    where
    lemma : ∀ (x₂ : Nat × Nat) →
      Pair (All (\ n → n ≤ Pair.fst x₂) (i :: xs))
      (Pair.fst x₂ ∈ (i :: xs)) →
      ∀ x₃ → Pair ⊤ (Pair (x₃ ≡ i) (x₃ ≡ i)) →
      Pair (All (\ n → n ≤ Pair.fst x₂) (x₃ :: x :: xs))
      (Pair.fst x₂ ∈ (x₃ :: x :: xs))
    lemma x₂ (AllCons x₁ fst , ∈Head) .i (_ , (refl , refl)) = (AllCons x₁ (AllCons (<⇒≤ x<i) fst)) , ∈Head
    lemma x₂ (AllCons x₁ fst , ∈Tail snd) _ (_ , (refl , refl)) = (AllCons x₁ (AllCons (≤-trans (<⇒≤ x<i) x₁) fst)) , ∈Tail (∈Tail snd)

  max'Proof2 : ∀ i x xs → (Succ x ≤ i → ⊥) →
    ∀ (P : Nat → Nat × Nat → Set) x₁ → Pair (Sigma ℕ (\ x₂ → Pair (Sigma ℕ (\ x₃
    → Pair ⊤ (Pair (x₃ ≡ i) (x₃ ≡ x₂)))) (x ≡ x₁))) (∀ x₂ → (∀ x₃ → Pair (Sigma
    ℕ (\ x₄ → Pair ⊤ (Pair (x₄ ≡ i) (x₄ ≡ x₃)))) (x ≡ x₁) → ∀ x₄ → Pair ⊤ (Pair
    (x₄ ≡ i) (x₄ ≡ x₃)) → Pair (All (\ n → n ≤ Pair.fst x₂) (x₄ :: x :: xs))
    (Pair.fst x₂ ∈ (x₄ :: x :: xs))) → P x₁ x₂) → Pair ⊤ (∀ x₂ → Pair (All (\ n
    → n ≤ Pair.fst x₂) (x₁ :: xs)) (Pair.fst x₂ ∈ (x₁ :: xs)) → P x₁ x₂)
  max'Proof2 i x xs x≥i P .x ((.i , ((.i , (fst₂ , (refl , refl))) , refl)) , snd) = tt , \ x₄ x₁ → snd x₄ (lemma x₄ x₁)
    where
    lemma : ∀ (x₄ : Pair Nat Nat) → Pair (All (\ n → n ≤ Pair.fst x₄) (x :: xs))
      (Pair.fst x₄ ∈ (x :: xs)) → ∀ x₃ → Pair (Sigma ℕ (\ x₅ → Pair ⊤ (Pair (x₅
      ≡ i) (x₅ ≡ x₃)))) (x ≡ x) → ∀ x₅ → Pair ⊤ (Pair (x₅ ≡ i) (x₅ ≡ x₃)) → Pair
      (All (\ n → n ≤ Pair.fst x₄) (x₅ :: x :: xs)) (Pair.fst x₄ ∈ (x₅ :: x :: xs))
    lemma (_ , _) (AllCons x fst , ∈Head) _ ((_ , (_ , (refl , refl))) , refl) _ (_ , (refl , refl)) = (AllCons (≮⇒≥ x≥i) (AllCons x fst)) , (∈Tail ∈Head)
    lemma x₄ (AllCons x₁ fst , ∈Tail snd) _ ((_ , (_ , (refl , refl))) , refl) _ (_ , (refl , refl)) = (AllCons (≤-trans (≮⇒≥ x≥i) x₁) (AllCons x₁ fst)) , (∈Tail (∈Tail snd))

  maxSpec' = [[ K ⊤ , maxPost' ]]
\end{code}
%endif
%{
%if style == poly
%format max' = max
%endif
Now we can finally turn our attention to completing our
derivation. Here is where using an \emph{interactive} proof assistant
such as Agda is invaluable. We begin by performing induction on the
input list, and splitting our goal accordingly. We can then repeatedly
fill in parts of the program, one command at a time, inspecting the
remaining derivation problem as we go. Along the way, we can call the
|refineDerivation| lemma to simplify any open specifications, if they
grow too complex. Indeed, if we replace the proofs in our derivation
with ellipses, we can read off the program we have calculated
directly:
\begin{code}
  max' : (xs : List Nat) -> Derivation (intros maxSpec' xs)  
  max' Nil        =  Step Get \ i →
                     Done i (ldotsHere((max'ProofNil i)))
  max' (x :: xs)  =  Step Get \ i →
                     if' x <? i
                       then  (\  lt   -> (ldotsHere(refineDerivation (max'Proof1 x xs i lt))) (max' xs))
                       else  (\  geq  -> Step (Put x) (hiddenConst((ldotsHere(refineDerivation (max'Proof2 i x xs geq)) (max' xs)))))
\end{code}
% }
The proof steps themselves are not particularly hard. In both
recursive calls, we need to perform a call to the |refineDerivation|
lemma and prove that the result of the call is strong enough to
fulfil the current proof goal. In the base case, we can give a direct
proof that the current state |i| satisfies the desired specification.

One result of formulating the |step| function in terms of the
predicate transformers |tril| and |trir| is that the new goals after
issuing a particular command are computed automatically from these
definitions, but may be more verbose than what a programmer might
write by hand, for example, by containing superfluous equalities
between intermediate states. We could avoid this by defining custom
transformations on our specifications for |put| and |get| directly, at
the expense of losing some generality. Nonetheless, it is encouraging
to see that we can calculate a program \emph{together with} our proof
assistant, rather than verify a program post-hoc.
%if style == newcode
\begin{code}
  max : DerivationFun [[ maxPre , maxPost ]]
  max xs = refineDerivation (maxProof xs) (max' xs)
\end{code}
%endif
\section{Discussion}
\label{sec:discussion}

Throughout this paper, we have had to choose between presenting the
most general definition possible and a less general choice, that
sufficed for the examples we intended to cover. When possible, we
have favoured simplicity over generality. For instance, the type of
our specifications can be generalised even further, making the
postcondition dependent on the precondition:
\begin{spec}
  record Spec (a : Set) (b : a -> Set) : Set where
    field
      pre : a -> Set
      post : (x : a) -> pre x -> b x -> Set
\end{spec}
The resulting definition is that of an \emph{indexed
  container}~\cite{indexed}. We have chosen to present a simply-typed
version of a function---even if a more general dependently typed
alternative exists---when the added generality was unnecessary for our
examples.

Throughout this paper, we have not concerned ourselves with issues of
size. Yet some of our definitions, such as those for specifications
and derivations, are too large to live in |Set|. In the accompanying
Agda development, we show how a suitable choice of universe level can
be used to stratify these definitions; for the sake of presentation,
however, we have ommitted these annotations in the code in this paper.


\subsection*{Related work}
\label{sec:related-work}

Traditionally, reasoning about pure functional programs is done
through equational reasoning. There are several attempts to extend
these techniques to the kinds of effectful programs we have presented in
this paper~\cite{gibbons, gibbons-hinze, hutton2008reasoning}.

There is a great deal of work studying how to reason about effects in
type theory~\cite{nanevski1, nanevski2,
  nanevski3, beauty, swierstra-phd, hoare-wouter, brady-effects}.
F$\star$ has introduced the notion of
Dijkstra monads~\cite{fstar, dijkstra-monad} to collect the
verification conditions arising from a program using a weakest
precondition semantics. The |wpSpec| function corresponds to the
predicate transformer semantics that F$\star$ associates with
specifications~\cite{dijkstra-free,multi-monadic}. The
compositionality results presented here correspond to subtyping of the
sequential composition in F$\star$. Where F$\star$ typically uses an SMT solver
to resolve verification conditions, the use of an interactive theorem
prover and higher-order logic may facilitate the verification of
properties that are difficult to encode in the SMT solver's
logic. More recently, \citet{maillard} have investigated the predicate
transformer and specification semantics of effectful programs, similar
to the effects presented here.

There is also a great deal of existing work on using interactive
theorem provers to perform program calculation. \citet{old-hol} have
given a formalisation of several notions, such as weakest precondition
semantics and the refinement relation, in the interactive theorem
prover HOL. This was later extended to the \emph{Refinement
  Calculator}~\cite{butler}, that built a new GUI on top of
HOL. ~\citet{dongol} have extended these ideas even further in HOL,
adding a separation logic and its associated algebraic
structure. \citet{boulme} has given a direct embedding of the
refinement calculus in Coq.
\citeauthor{alpuim2}~\citeyearpar{alpuim2,alpuim1} have given an
similar development to the one presented here, tailored specifically
to stateful computations. \citet{snapl} have recently proposed using
the Coq proof assistants to derive correct programs from their
specification. Their work
on the Fiat framework is geared towards describing \emph{data refinement}
and the synthesis of abstract datatypes, packaging methods and data.

\subsection*{Further work}
\label{sec:further-work}

This paper does not yet consider \emph{combinations} of different
effects.  In principle, however, we believe it should be possible to
take the coproduct of our free monads in the style of \citet{swierstra2008}
to combine the different effects
syntactically. We hope that the composition of predicate transformers
can be used to assign semantics to programs using a variety of
different effects---much as we defined a semantics of mixed programs
and specifications from their constituent parts. Similar ideas have
already been explored when embedding algebraic effects in Haskell by
\citet{Wu2014}.

%\todo{Nail down theory further -- presheaves, contravariant Set-valued hom
%  functors, yoneda embedding, etc}

There are well-known efficiency problems when working with free monads
directly, as we have done here. While efficiency was never our primary
concern, we hope that we might adapt existing solutions to avoid these
issues~\cite{janis,freer}.

\subsection*{Conclusions}
We have presented several small example
programs and verified their correctness. The aim of these examples is
to \emph{illustrate} our definitions and \emph{validate} our design
choices, rather than solve any realistic verification challenge. There
is a great deal of further engineering work necessary to ensure these
ideas scale easily beyond such simple examples: custom tactics and
notation could help facilitate program calculation; further proof
automation is necessary to keep the complexity of intermediate
calculations in check. Nonetheless, we believe that the predicate
transformer semantics defined in this paper offer a \emph{functional}
account of effects that is worth exploring further.



% \item wp (s,q) or wp (s,p) implies wp(s,q or p) -- but not the other
%   way around. The implication in the other direction only holds when
%   the program is deterministic.
\begin{acks}
  We would like to thank the members of Utrecht University's Software
  Technology Reading Group and the members of IFIP WG 2.1 for feedback
  on this work. Furthermore, the ICFP reviewers provided us with
  insightful and detailed feedback for which we are most grateful.
\end{acks}

\DeclareRobustCommand{\tussenvoegsel}[2]{#2}
\bibliography{handlers}


\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 


