\section{de Bruijn Representation}

%if False
\begin{code}
module DeBruijn where

open import Agda.Primitive renaming (_⊔_ to _\-/_)

\end{code}
%endif

In 1999, Altenkirch and Reus gave a de Bruijn treatment of simply
typed $\lambda$-calculus, together with an implementation of simultaneous
substitution~\cite{altenkirch.reus:monads.lambda}. Let us review how it goes.

The simple types are given inductively.

%format Set = "\D{Set}"
%format Type = "\D{Ty}"
%format base = "\C{base}"
%format ->>  = "\mathrel{\C{\supset}}"
%format _->>_ = "\C{" _ "\!}" ->> "\C{\!" _ "}"
\begin{code}
infixr 30 _->>_

data Type : Set where
  base   : Type
  _->>_  : Type -> Type -> Type
\end{code}

In Agda, infix operators are named with \-/ in their argument places.
Types are arranged in backwards (`\emph{snoc}-') lists to
form \emph{contexts}.

%format Bwd = "\D{Bwd}"
%format [] = "\C{[]}"
%format -, = "\mathbin{\C{\mathrm{-\hspace*{-0.03in},}}}"
%format _-,_ = "\C{" _ "\!}" -, "\C{\!" _ "}"
%format Context = "\D{Cx}"
\begin{code}
infixl 20 _-,_

data Bwd (X : Set) : Set where
  []    : Bwd X
  _-,_  : Bwd X -> X -> Bwd X

Context = Bwd Type
\end{code}

\begin{craft}[Backwards Lists]
Forwards lists are much more commonplace in functional programming,
but I have learned the hard way to use a separate type for lists
which grow on the right. The cognitive cost of interpreting lists
in reverse is higher, at times, than I can pay: I make mistakes.
I also choose symbols for `snoc' and `cons' which avoid misleading
reflectional symmetry and have modest pictographic value.
\end{craft}

Typed de Bruijn indices select \emph{one} entry from a context.
%format <<- = "\mathrel{\D{\shortleftarrow}}"
%format _<<-_ = "\D{" _ "\!}" <<- "\D{\!" _ "}"
%format <<-_ = <<- "\D{\!" _ "}"
%format _<<- = "\D{" _ "\!}" <<-
%format <<1- = "\mathrel{\D{\shortleftarrow}}"
%format _<<1-_ = "\D{" _ "\!}" <<1- "\D{\!" _ "}"
%format <<1-_ = <<1- "\D{\!" _ "}"
%format _<<1- = "\D{" _ "\!}" <<1-
%format ze = "\C{ze}"
%format su = "\C{su}"
%format Ga = "\V{\Gamma}"
%format De = "\V{\Delta}"
%format sg = "\V{\sigma}"
%format ta = "\V{\tau}"
%format !!1- = "\mathrel{\D{\vdash}}"
%format _!!1-_ = "\D{" _ "\!}" !!1- "\D{\!" _ "}"
%format !!1-_ = !!1- "\D{\!" _ "}"
%format !!- = "\mathrel{\D{\vdash}}"
%format _!!-_ = "\D{" _ "\!}" !!- "\D{\!" _ "}"
%format !!-_ = !!1- "\D{\!" _ "}"
%format va = "\C{va}"
%format ap = "\C{ap}"
%format la = "\C{la}"
\begin{code}
infix 10 _<<1-_

data _<<1-_ (ta : Type) : Context -> Set where
  ze  : {-<-} forall {Ga} -> {->-}     ta <<1- Ga -, ta
  su  : {-<-} forall {Ga sg} -> {->-}  ta <<1- Ga
      ->                               ta <<1- Ga -, sg
\end{code}

\begin{craft}[Parameters, Uniform Indices, Restrictable Indices]
In the |data| declaration of an Agda type former, some things are
declared left of |:| and scope over the whole declaration. They
must be used \emph{uniformly} in the \emph{return} types of value
constructors. They are, however, free to vary in the types of
recursive substructures. If they do so vary, we call them \emph{uniform}
indices. Only if they remain constant throughout should we refer to
them as \emph{parameters}. So, |ta|, above is a parameter, but |Ga|, below
is a uniform index. The distinction impacts the category in which an
initial object is being constructed. |(ta <<1-_)| is constructed in
|Context -> Set|, while |_!!1-_| is constructed in
|Context -> Type -> Set|. Meanwhile, right of |:| come those things
which may be restricted to particular patterns of value in the return
types of value constructors, e.g., \emph{nonempty} contexts above,
and \emph{function} types below.
\end{craft}

The type of terms reflect the typing rules, indexed by a context and
the type being inhabited.

\begin{code}
infix 10 _!!1-_

data _!!1-_ (Ga : Context) : Type -> Set where

  va  : {-<-} forall {ta} -> {->-}     ta <<1- Ga
      ->                               Ga !!1- ta

  ap  : {-<-} forall {sg ta} -> {->-}  Ga !!1- sg ->> ta
      ->                               Ga !!1- sg
      ->                               Ga !!1- ta

  la  : {-<-} forall {sg ta} -> {->-}  Ga -, sg !!1- ta
      ->                               Ga !!1- sg ->> ta
\end{code}

Observe that the context we are handed at the root of a term only ever gets
larger, each time we use a |la|mbda. Only when we reach a |va|riable do we
choose one thing from the context and disregard the rest.

Now, a \emph{simultaneous substitution} is a type-respecting mapping from
variables in some source context |Ga| to terms over target context |De| ---
from |(_<<1- Ga)| to |(De !!1-_)|, if you will. When we push such a thing
under |la|, we need instead a mapping from
|(_<<1- Ga -, sg)| to |(De -, sg !!1-_)|. We can map the newly bound |ze| to
|va ze|, but the trouble is that all of |Ga|'s variables are mapped to terms
over |De|, not |De -, sg|. It is thus necessary to traverse all those terms
and adjust their leaves, because it is only at the leaves that we document
\emph{non}-usage of variables. Shift happens.

Worse, if we attempt to carry out the shift by simultaneous
substitution, we leave the comfortable territory of structural
recursion and have some explaining to do. It is useful to observe that
shifts are merely simultaneous (order-preserving, injective) renumberings
which may readily act on terms. Once we have simultaneous renumbering
available, simultaneous substitution is easy. Moreover, they are very
similar, so we may readily abstract the common structure, as I learned
from Goguen and McKinna and demonstrated in my
thesis~\cite{goguenmckinna,DBLP:phd/ethos/McBride00}.

Shifts --- simultaneous renumberings --- are the problem, but they are also
the key to the solution.

