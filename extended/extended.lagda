\documentclass[a4paper,superscriptaddress,11pt,shorttitle=template]{compositionalityarticle}
\pdfoutput=1
\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage[T1]{fontenc}
\usepackage{amsmath}
\usepackage{hyperref}

\usepackage{tikz}
\usepackage{lipsum}

\usepackage{upgreek}
\usepackage{xypic}

\usepackage{pig}
\ColourEpigram
\newcommand{\D}[1]{\blue{\ensuremath{\mathsf{#1}}}}
\newcommand{\C}[1]{\red{\ensuremath{\mathsf{#1}}}}
\newcommand{\F}[1]{\green{\ensuremath{\mathsf{#1}}}}
\newcommand{\V}[1]{\purple{\ensuremath{\mathit{#1}}}}
\newcommand{\M}[1]{\black{\ensuremath{\mathrm{#1}}}}

\newtheorem{theorem}{Theorem}
\newtheorem{craft}[theorem]{Craft}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{lemma}[theorem]{Lemma}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%format inductive = "\mathkw{inductive}"
%format constructor = "\mathkw{constructor}"
%format pattern = "\mathkw{pattern}"
%format rewrite = "\mathkw{rewrite}"
%format syntax = "\mathkw{syntax}"
%format forall = "\D{\forall}"
%format . = "."

%format sb0 = "_{\V{0}}"
%format sb1 = "_{\V{1}}"
%format sb2 = "_{\V{2}}"
%format sb3 = "_{\V{3}}"
%format sb01 = "_{\V{01}}"
%format sb12 = "_{\V{12}}"
%format sb23 = "_{\V{23}}"
%format sb02 = "_{\V{02}}"
%format sb13 = "_{\V{13}}"
%format sb03 = "_{\V{03}}"
%format sb012 = "_{\V{012}}"
%format sb013 = "_{\V{013}}"
%format sb023 = "_{\V{023}}"
%format sb123 = "_{\V{123}}"


%if False
\begin{code}
open import Agda.Primitive renaming (_⊔_ to _\-/_)
\end{code}
%endif

%format \-/ = "\mathbin{\D{\sqcup}}"

\begin{document}

\title{CodeBruijn Programming, Categorically}
\date{}
\author{Conor Mc Bride}
\email{conor@@strictlypositive.org}
\homepage{http://strictlypositive.org}
\orcid{0000-0003-1487-0886}
%\thanks{}
\affiliation{Mathematically Structured Programming, Computer \& Information Sciences, University of Strathclyde, Scotland}
\maketitle

\begin{abstract}
  I'll write this later when I know what I'm saying.
\end{abstract}

CodeBruijn (``co de Bruijn'') programming is a methodology for
representing and manipulating syntax in a nameless way, like de Bruijn
representation~\cite{deBruijn:dummies}, but making the opposite
canonical choice for exposing the \emph{non}-use of variables.
The essence of the idea is to restrict the \emph{scope} (which variables
\emph{may} occur free) of a term to its \emph{support} (which variables
\emph{do} occur free). Variables are expelled from scope at the roots of
maximal subtrees in which they are not used, where de Bruijn representation
keeps variables in scope from their binding sites all the way to the leaves,
i.e., the minimal subtrees in which they are not used. The codeBruijn
approach thus relies on the maintenance of subtle invariants, reminiscent
of Kennaway and Sleep's `director strings' representation~\cite{DBLP:journals/ipl/KennawayS87}. Dependently typed programming languages such as Agda~\cite{DBLP:conf/afp/Norell08} readily taken on the task of minding that business for us. This paper shows how, and hopefully, why.

The key structure at work is the semi-simplicial category on scopes,
i.e., the category of order-preserving embeddings (colloquially,
`thinnings') from one scope to another. From Bellegarde and
Hook~\cite{bellegarde.hook:substitution.monad}, via Bird and
Paterson~\cite{bird.paterson:debruijn.nested}, and Altenkirch and
Reus~\cite{altenkirch.reus:monads.lambda}, it has become a commonplace
to index types of terms by their scopes. Such types should really be
thought of as `thinnables' --- \emph{functors} from the thinnings ---
because thinnings act compositionally on terms. The operation of
mapping a scope to its identity thinning induces a forgetful functor
from thinnables to scope-indexed types. This forgetful functor has a
celebrated right adjoint, amounting to abstraction over all scopes
into which one's own embeds, which is the basis of Altenkirch, Hofmann
and Streicher's Kripke-model construction which drives normalization
by evaluation ~\cite{DBLP:conf/ctcs/AltenkirchHS95}. But, being a
forgetful functor, one should ask after its \emph{left} adjoint.
That exists, of course, and is the basis of codeBruijn programming: we
define \emph{relevant} terms, indexed by \emph{support}, then make them
\emph{freely} thinnable by attaching the thinning from support to scope
at the root of the term. Further thinnings act by composition at the root,
without traversing the term at all.

This paper is written as a literate Agda implementation of a
codeBruijn toolkit, structured categorically. I formalise the active
categorical abstractions, given provocation from the task at hand. I have
adopted something of a tutorial style, partly because there is some novelty
in teaching category theory to functional programmers with examples which are
not sets-and-functions, but mostly because I am teaching myself. I hope it
is also a useful engagement with dependently typed programming, for category
theorists. I shall certainly draw the \emph{diagrams} which drive the
constructions. There will also be some transferable lessons about programming
`craft' which I shall seek to draw out.


\section{de Bruijn Representation}

In 1999, Altenkirch and Reus gave a de Bruijn treatment of simply
typed $\lambda$-calculus, together with an implementation of simultaneous
substitution~\cite{altenkirch.reus:monads.lambda}. Let us review how it goes.

The simple types are given inductively.

%format Set = "\D{Set}"
%format -> = "\mathrel{\D{\to}}"
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

In Agda, infix operators are named with |_| in their argument places.
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
%format ze = "\C{ze}"
%format su = "\C{su}"
%format Ga = "\V{\Gamma}"
%format De = "\V{\Delta}"
%format sg = "\V{\sigma}"
%format ta = "\V{\tau}"
%format !!- = "\mathrel{\D{\vdash}}"
%format _!!-_ = "\D{" _ "\!}" !!- "\D{\!" _ "}"
%format !!-_ = !!- "\D{\!" _ "}"
%format va = "\C{va}"
%format ap = "\C{ap}"
%format la = "\C{la}"
\begin{code}
infix 10 _<<-_

data _<<-_ (ta : Type) : Context -> Set where
  ze  : {-<-} forall {Ga} -> {->-}     ta <<- Ga -, ta
  su  : {-<-} forall {Ga sg} -> {->-}  ta <<- Ga
      ->                               ta <<- Ga -, sg
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
initial object is being constructed. |(ta <<-_)| is constructed in
|Context -> Set|, while |_!!-_| is constructed in
|Context -> Type -> Set|. Meanwhile, right of |:| come those things
which may be restricted to particular patterns of value in the return
types of value constructors, e.g., \emph{nonempty} contexts above,
and \emph{function} types below.
\end{craft}

The type of terms reflect the typing rules, indexed by a context and
the type being inhabited.

\begin{code}
infix 10 _!!-_

data _!!-_ (Ga : Context) : Type -> Set where

  va  : {-<-} forall {ta} -> {->-}     ta <<- Ga
      ->                               Ga !!- ta

  ap  : {-<-} forall {sg ta} -> {->-}  Ga !!- sg ->> ta
      ->                               Ga !!- sg
      ->                               Ga !!- ta

  la  : {-<-} forall {sg ta} -> {->-}  Ga -, sg !!- ta
      ->                               Ga !!- sg ->> ta
\end{code}

Observe that the context we are handed at the root of a term only ever gets
larger, each time we use a |la|mbda. Only when we reach a |va|riable do we
choose one thing from the context and disregard the rest.

Now, a \emph{simultaneous substitution} is a type-respecting mapping from
variables in some source context |Ga| to terms over target context |De| ---
from |(_<<- Ga)| to |(De !!-_)|, if you will. When we push such a thing
under |la|, we need instead a mapping from
|(_<<- Ga -, sg)| to |(De -, sg !!-_)|. We can map the newly bound |ze| to
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


\section{Thinnings}

\begin{definition}[Thinnings]
We may define the thinnings, i.e., the order-preserving embeddings,
our simultaneous renumberings, as follows:

%format <= = "\mathrel{\D{\le}}"
%format _<=_ = "\D{" _ "\!}" <= "\D{\!" _ "}"
%format -^ = "\mathbin{\C{\mathrm{-\hspace*{-0.06in}\raisebox{-0.04in}{\^{}}}}}"
%format _-^_ = "\C{" _ "\!}" -^ "\C{\!" _ "}"
%format ga = "\V{\gamma}"
%format de = "\V{\delta}"
%format ze = "\V{\zeta}"
\begin{code}
module _ {X : Set} where  -- fix a set |X| of \emph{sorts}, e.g., |Type|

  infix 10 _<=_
  infixl 20 _-^_

  data _<=_ : Bwd X ->                       Bwd X -> Set where

    _-^_  :   {-<-} forall {ga de} -> {->-}  ga       <= de
          ->  forall x ->                    ga       <= de -, x

    _-,_  :   {-<-} forall {ga de} -> {->-}  ga       <= de
          ->  forall x ->                    ga -, x  <= de -, x

    []    :                                  []       <= []
\end{code}
\end{definition}

I am careful to speak of our backward lists as \emph{scopes}, rather than
\emph{contexts}, as it is not necessary for them to document the \emph{types}
of the variables for this machinery to work.

We lift the constructors from lists to represent the situation
where parts of the source scope are copied to the target, but we also
introduce |-^| to insert an extra element in the target.

Electronic engineers will notice that a thinning is more or less a vector
of bits, with |-^| for 0 and |-,| for 1, but it is indexed by its
\emph{population} --- the entries marked 1. Expect Boolean operations.

%format io = "\F{\upiota}"
\begin{definition}[identity thinnings, |io|]
Let us observe that identity thinnings exist, copying their scope.

\begin{code}
  io : forall {ga} -> ga <= ga
  io {[]}       = []
  io {ga -, x}  = io {ga} -, x
\end{code}
\end{definition}

\begin{craft}[Implicits]
Agda uses curly braces to mark arguments which are normally suppressed.
In general, it is sensible to adopt the suppression convention
appropriate for the expected \emph{use} sites. Here, the fact that |<=| is a type constructor means
that |ga| will be determined if the type is given in advance.
Often, we then have to use an explicit override at definition sites. 
This sort of thing never happens in Hindley-Milner
languages because any information for which inference is permitted is
guaranteed to be operationally useless. The inference of operationally
useful information represents progress.
\end{craft}

Further, thinnings compose. I write composition diagrammatically.

%format -fake = "\mathbin{\F{\fatsemi}}"
%format _-fake_ = "\F{" _ "\!}" -fake "\F{\!" _ "}"

\begin{definition}[thinning composition, |-fake|]
Thinnings fore and aft compose thus:

%format th = "\V{\theta}"
%format ph = "\V{\phi}"
%format ps = "\V{\psi}"
\begin{code}
  infixl 20 _-fake_

  _-fake_ : {-<-} forall {ga de ze} -> {->-} ga <= de -> de <= ze -> ga <= ze
  th         -fake (ph -^ x)  = th -fake ph -^ x
  (th -^ x)  -fake (ph -, x)  = th -fake ph -^ x
  (th -, x)  -fake (ph -, x)  = th -fake ph -, x
  []         -fake []         = []
\end{code}
\end{definition}

\begin{craft}[Operator Priority and Association]
My habit is to arrange priority and association
so that computation results in net decrease of parentheses.
\end{craft}

\begin{craft}[Laziness and Definitional Equality]
Working in intensional type theories like Agda involves a certain
amount of care with the equational properties of programs --- the typechecker
will run these programs, as defined, on open terms.
So the order of the lines in the above program matters. If the aft-thinning
inserts, there is no call to inspect the fore-thinning. Only if the aft
thinning copies need we ask what the fore-thinning gives us. If the first
line is moved later, the function becomes unnecessarily strict in the
fore-thinning, and definitional equality loses power.
\end{craft}

The reader should note that I will shortly substitute a subtly different
definition of composition for this one. Rest assured that its replacement
will satisfy the above equations.


\section{When `Green Slime' is Bad, Avoid It}

We are accustomed to reasoning by \emph{equation}.

%format ~ = "\mathrel{\D{\sim}}"
%format _~_ = "\D{" _ "\!}" ~ "\D{\!" _ "}"
%format r~ = "\C{r\!\!\sim}"

\begin{definition}[Inductive Equality, |~|]
In Agda, we may give an inductive definition of equality,
as follows:
\begin{code}
infix 5 _~_
data _~_ {l}{X : Set l}(x : X) : X -> Set l where
  r~ : x ~ x
\end{code}
The |l| parameter is an arbitrary \emph{level} in the
Russell-style hierarchy: |Set| abbreviates |Set 0|;
|Set 0 : Set 1|, and so on.
%if False
\begin{code}
{-# BUILTIN EQUALITY _~_ #-}
\end{code}
%endif
\end{definition}

The above definition is \emph{intensional}, in that we
can give canonical evidence that |x ~ y| only if |x| and
|y| have the same \emph{implementation}, up to definitional
equality. We shall have trouble because of that, in what is
to follow, but that is not the trouble I mean to discuss in
this section.

Suppose we have an hypothesis |q : th -fake ph ~ ps -, x|.
We ought to be able to deduce that |th| and |ph| are both
made by |(_-, x)|. However, pattern matching on the equality
proof |q| will fail, because it is not clear how to unify
|th -fake ph| with |ps -, x|, unless we are gifted with the
power to run functions backwards, which Agda is not. Our
only option is to \emph{remember} how |-fake| computes, then
match on |ph| and |th|, eliminating the impossible cases
which arise by refuting |q|.

`Green slime' is a colloquialism for expressions involving
recursively defined functions which do not compute to
canonical form. It is toxic to unification, as it unifies
only with variables (purple things). Fortunately, there
are strategies to avoid it.

%format grf = "\F{f}"
%format blF = "\D{F}"
%format bks = "s"
%format bkt = "t"
\begin{craft}[Inductive Relations are Invertible]
It is often useful to replace equations |grf bks ~ bkt|
with relations |blF bks bkt|, where |blF| is defined
inductively to be the \emph{graph} of |f|.
\end{craft}

Let us put this into practice at once!

\begin{definition}[composition triangle]
Reading from the definition of |-fake|, construct its
graph, thus:
%format CTL = "\D{\ulcorner}\,"
%format CTM = "\,\D{\fatsemi}\,"
%format CTR = "\,\D{\urcorner\!\!\sim}\,"
%format (CTri (th) (ph) (ps)) = CTL th CTM ph CTR ps
%format (CTS1 (ph) (ps)) = (CTL _ CTM ph CTR ps)
%format (CTS2 (th) (ps)) = (CTL th CTM _ CTR ps)
%format (CTS3 (th) (ph)) = (CTL th CTM ph CTR _)
%format -^, = "\mathbin{\C{\mathrm{-\hspace*{-0.06in}\raisebox{-0.04in}{\^{}}\hspace*{-0.03in},}}}"
%format _-^,_ = "\C{" _ "\!}" -^, "\C{\!" _ "}"

%if False
\begin{code}
module _ {X : Set} where
\end{code}
\begin{code}
  infixl 20 _-^,_

  data CTri : {-<-} forall {ga de ze : Bwd X} -> {->-} (th : ga <= de)(ph : de <= ze)(ps : ga <= ze) -> Set where

    _-^_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     (CTri th         ph         ps)
           -> forall x ->                                                                                       (CTri th         (ph -^ x)  (ps -^ x))

    _-^,_  : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     (CTri th         ph         ps)
           -> forall x ->                                                                                       (CTri (th -^ x)  (ph -, x)  (ps -^ x))

    _-,_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     (CTri th         ph         ps)
           -> forall x ->                                                                                       (CTri (th -, x)  (ph -, x)  (ps -, x))

    []     :                                                                                                    (CTri []         []         [])

  CTS1 = \ {ga}{de}{ze} ph ps th -> CTri {ga}{de}{ze} th ph ps
  CTS2 = \ {ga}{de}{ze} th ps ph -> CTri {ga}{de}{ze} th ph ps
  CTS3 = CTri
\end{code}
%endif
\begin{spec}
  infixl 20 _-^,_

  data CTL _ CTM _ CTR _ : {-<-} forall {ga de ze : Bwd X} -> {->-} (th : ga <= de)                             (ph : de <= ze)(ps : ga <= ze) -> Set where

    _-^_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     CTL th         CTM ph       CTR ps
           -> forall x ->                                                                                       CTL th         CTM ph -^ x  CTR ps -^ x

    _-^,_  : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     CTL th         CTM ph       CTR ps
           -> forall x ->                                                                                       CTL th -^ x    CTM ph -, x  CTR ps -^ x

    _-,_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     CTL th         CTM ph       CTR ps
           -> forall x ->                                                                                       CTL th -, x    CTM ph -, x  CTR ps -, x

    []     :                                                                                                    CTL []         CTM []       CTR []
\end{spec}
\end{definition}

And there was nothing green to be seen! The only green things on the right in the
definition of |-fake| were recursive calls to |-fake|, and these we have replaced
by variables.

I call inhabitants of |(CTri th ph ps)|
\emph{composition triangles} exactly because they witness the commutation of the
diagram
\[\xymatrix{
                        & |ze| \\
  |de| \ar[ru]^{|ph|}   &      \\
                        & |ga| \ar[lu]^{|th|}\ar[uu]_{|ps|}\\
}\]
Now let us get our hands on them. You might think that the thing to do is to prove
\[
|(th : ga <= de)(ph : de <= ze) -> (CTri th ph (th -fake ph))|
\]
but that amounts to implementing composition a \emph{third} time, as well as being
pragmatically suboptimal, as I shall explain later. A better move is to reimplement
|-fake| by proving, morally,
\[
|(th : ga <= de)(ph : de <= ze) ->| \;\mbox{`$\exists |ps|.$'}\; |(CTri th ph ps)|
\]
We shall have need of existential quantification!

%format Sg = "\D{\Upsigma}"
\begin{definition}[Dependent Pair Types, Unit Type]
Dependent pair types (|Sg|-types, in the jargon) may be introduced as
\emph{records}, where the
type of the second projection depends on the value of the first. The definition
is polymorphic in the type theoretic hierarchy.
%format Sg = "\D{\Upsigma}"
%format [* = "(\!"
%format :: = ":"
%format ]* = "\!)\mathrel{\D{\times}}"
%format , = "\C{,}"
%format _,_ = "\C{" _ "}" , "\C{" _ "}"
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format One = "\D{One}"
%format <> = "\C{\langle\rangle}"
\begin{code}
infixr 5 _,_

record Sg {k l}(S : Set k)(T : S -> Set l) : Set (l \-/ k) where
  constructor _,_
  field  fst  : S
         snd  : T fst
open Sg public     -- brings the projections into scope

syntax Sg S (\ x -> T) = [* x :: S ]* T

record One {l} : Set l where constructor <>
\end{code}
It is convenient to sugar dependent pair types as a binding form,
after the fashion of dependent
function types\footnote{Agda does not let you do precisely this, but \LaTeX{} does
the rest.}.
\end{definition}

Three commonly occurring variations merit abbreviation.
%format * = "\mathbin{\D{\times}}"
%format _*_ = "\D{" _ "\!}" * "\D{\!" _ "}"
%format :* = "\mathbin{\D{\dot\times}}"
%format _:*_ = "\D{" _ "\!}" :* "\D{\!" _ "}"
%format < = "\D{\langle}"
%format > = "\D{\rangle}"
%format <_> = < "\D{\!" _ "\!}" >
\begin{code}
_*_ : {-<-}forall {k l} ->{->-} Set k -> Set l -> Set (l \-/ k)
S * T = [* _ :: S ]* T
_:*_ : {-<-}forall {k l} ->{->-} {S : Set k}(P Q : S -> Set l) -> (S -> Set l)
(P :* Q) s = P s * Q s
<_> : {-<-}forall {k l}{->-} {S : Set k}(P : S -> Set l) -> Set (l \-/ k)
< P > = [* x :: _ ]* P x
\end{code}
The first of these is ordinary non-dependent pairing. The second is its
pointwise lifting to `predicates': |P :* Q| holds whenever |P| holds and |Q| holds.
The third, prounounced
`possibly |P|' or `something is |P|',
asserts that a `predicate' (i.e., a function to |Set l|) is
somehow satisfied: the domain of the predicate is elided.
Now we can write |< P :* Q >| for `something is both |P| and |Q|'.

\begin{craft}[Mixfix Operator Sections, Pattern Synonyms]
The relation |CTL _ CTM _ CTR _| is given in mixfix form exactly because Agda
supports operator sections --- |(CTS1 ph ps)|, |(CTS2 th ps)| and |(CTS3 th ph)|
--- which are predicates designed to be used with |<_>|. We can write
%format th0 = th sb0
%format th1 = th sb1
%format ph0 = ph sb0
%format ph1 = ph sb1
\[
  |<(CTS3 th0 ph0) :* (CTS3 th1 ph1)>|
\]
to assert the existence of a commuting square. Very often, the existential witness
is not important. Agda provides the means to elide it:
%format & = "\C{\dot{,}}\,"
%format _&_ = "\C{" _ "}" & "\C{" _ "}"
\begin{code}
infixr 6 _&_
pattern _&_ p q = _ , p , q
\end{code}
A \emph{pattern synonym} is essentially a macro which can be used on either side
of the |=| sign: in this case, we ignore the existential witness on the left and
demand its synthesis on the right.
\end{craft}

%format -<= = -fake
%format _-<=_ = _-fake_
%format <-> = "\mathbin{\F{\langle\fatsemi\rangle}}"
%format _<->_ = "\F{" _ "\!}" <-> "\F{\!" _ "}"

\begin{lemma}[constructing composition triangles, |<->|]
If |th| and |ph| are thinnings which meet in the middle, it is possible to
construct their composition triangle. Accordingly,
we may redefine |-fake| to project the existential witness.
\begin{code}
infix 10 _<->_

_<->_ : {-<-} forall {X}{ga de ze : Bwd X} -> {->-} (th : ga <= de)(ph : de <= ze) -> <(CTS3 th ph)>
th       <-> ph -^ x  with _ , v <- th <-> ph  = _ , v -^ x
th -^ x  <-> ph -, x  with _ , v <- th <-> ph  = _ , v -^, x
th -, x  <-> ph -, x  with _ , v <- th <-> ph  = _ , v -, x
[]       <-> []                                = _ , []

_-<=_ : {-<-} forall {X}{ga de ze : Bwd X} -> {->-} ga <= de -> de <= ze -> ga <= ze
th -<= ph = fst (th <-> ph)
\end{code}
\end{lemma}

\begin{craft}[|with| Programs]
The |with| programming notation~\cite{DBLP:journals/jfp/McBrideM04}
%format vep = "\vec{p}"
%format vep1 = vep "_1"
%format vepn = vep "_n"
%format blp = "p"
%format blp1 = blp "_1"
%format blpn = blp "_n"
%format ble = "e"
%format ble1 = ble "_1"
%format blen = ble "_n"
%format vdots = "\vdots"
\begin{spec}
grf vep   with   ble
grf vep1  |      blp1  = ble1
          vdots
grf vepn  |      blpn  = blen
\end{spec}
allows us to extend the left-hand side of a program with an extra column for
the value of |ble|, so we may match patterns anywhere, refining the original
patterns |vep| as well as asking about |ble|. Usefully, |ble| is abstracted
from any types where it occurs, so matching on its value refines types, too.

By defining |-<=| as a projection of |<->|, we make |with th <-> ph| abstract
all occurrences of |-<=| at the same time as it yields up the composition
triangle. The same is true of any program defined as the existential witness
to the possibility of satisfying a specification.

The recently added notation, |with blp <- ble|, allows us to avoid introducing
a new line to the pattern match if there is only \emph{one} case, given by
|blp|.
\end{craft}

\begin{craft}[Invisible Programs]
Agda allows the `don't care' |_| to be used both in patterns, where it neglects to
ask a question, and in expressions, where it neglects to give an answer. In the
latter case, the missing term must be inferable by unification. In the case of
function graphs, the program already given in the relation determines by its
construction the missing existential witnesses. The composition \emph{function}
has all but disappeared!
\end{craft}

Now, composition triangles give the graph of a function, and functions are
deterministic, accordingly, we should be able to recover the fact that the
inputs determine both the output and the witness.

\begin{lemma}[Uniqueness of Composition Triangles]
For any given inputs |th| and |ph|, there is at most one |ps| and at most one
|v| such that |v : (CTri th ph ps)|.
%if False
\begin{code}
pattern splatr = r~
pattern splatrr = r~ , r~
pattern splatrr,rr = splatrr , splatrr
\end{code}
%endif
%format contraction = "\C{\star}"
%format splatr = contraction
%format splatrr = contraction
%format splatrr,rr = contraction
%format ~-~ = "\mathbin{\F{\sim\!\!\!\fatsemi\!\!\!\sim}}"
%format _~-~_ = "\F{" _ "\!}" ~-~ "\F{\!" _ "}"
%format v0 = v sb0
%format v1 = v sb1
%format ps0 = ps sb0
%format ps1 = ps sb1
%if False
\begin{code}
infix 10 _~-~_
_~-~_  : {-<-} forall {X}{ga de ze : Bwd X}{th : ga <= de}{ph : de <= ze}{ps0 ps1 : ga <= ze} -> {->-}  (v0 : (CTri th ph ps0))(v1 : (CTri th ph ps1))
       ->                                                                                               Sg (ps0 ~ ps1) \ { splatr -> v0 ~ v1 }
v0 -^ x   ~-~ v1 -^ x   with splatrr <- v0 ~-~ v1  = splatrr
v0 -^, x  ~-~ v1 -^, x  with splatrr <- v0 ~-~ v1  = splatrr
v0 -, x   ~-~ v1 -, x   with splatrr <- v0 ~-~ v1  = splatrr
[]        ~-~ []                                   = splatrr
\end{code}
%endif
\begin{spec}
infix 10 _~-~_
_~-~_  : {-<-} forall {X}{ga de ze : Bwd X}{th : ga <= de}{ph : de <= ze}{ps0 ps1 : ga <= ze} -> {->-}  (v0 : (CTri th ph ps0))(v1 : (CTri th ph ps1))
       ->                                                                                               [* (splatr) : ps0 ~ ps1 ]* v0 ~ v1
v0 -^ x   ~-~ v1 -^ x   with splatrr <- v0 ~-~ v1  = splatrr
v0 -^, x  ~-~ v1 -^, x  with splatrr <- v0 ~-~ v1  = splatrr
v0 -, x   ~-~ v1 -, x   with splatrr <- v0 ~-~ v1  = splatrr
[]        ~-~ []                                   = splatrr
\end{spec}
\end{lemma}

\begin{craft}[Dependent Equations]
The equation |v0 ~ v1| may look ill typed, but it is not. The inlined pattern match
in the dependent pair type causes |ps0| to unify with |ps1|. This can be quite a
convenient way to specify `telescopic' equations.
\end{craft}

\begin{craft}[Contraction Pattern, |contraction|]
In typeset code, I
write |contraction| instead of unique patterns which can be
constructed by record expansion followed by at most one step of case
analysis for each field. Matching with |contraction| collapses spaces
to a point. Agda does not yet support this feature. Here, it
abbreviates |r~ , r~|, but it can scale to much larger uninteresting
types.  \end{craft}

We have a notion of thinning, closed under identity and composition. I like to
visualize thinnings as two horizontal sequences of dots. Each dot on the bottom
 is joined to a dot on top by a vertical chord, but there may be dots on top with no
chord incident.
\[\begin{array}{ccccc}
  \bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
  \mid && \mid && \mid \vspace*{-0.17in}\\
  \bullet && \bullet && \bullet \\
\end{array}\]
The identity thinning has all chords present. Composition is vertical pasting,
followed by the contraction of chords which do not reach the bottom.
\[|io| \quad = \quad
  \begin{array}{ccccc}
  \bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
  \mid & \mid & \mid & \mid & \mid \vspace*{-0.17in}\\
  \bullet & \bullet & \bullet & \bullet & \bullet \\
\end{array}
\qquad\qquad\qquad\qquad
\begin{array}{cccccc}
        &\bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
        &\mid && \mid && \mid \vspace*{-0.17in}\\
        &\bullet && \bullet && \bullet \vspace*{-0.17in}\\
  |-<=| &\mid &&&& \mid  \vspace*{-0.17in}\\
        &\bullet &&&& \bullet
\end{array}
\quad = \quad
\begin{array}{ccccc}
  \bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
  \mid &&  && \mid \vspace*{-0.17in}\\
  \mid &&  && \mid \vspace*{-0.17in}\\
  \mid &&&& \mid  \vspace*{-0.17in}\\
  \bullet &&&& \bullet
\end{array}
\]
Spatial intuition makes it clear, informally, that identitied are absorbed and that
composition is associative. Let us make that intuition formal.

\begin{lemma}[Degenerate Triangles]
Every thinning |th| induces two degenerate triangles, where |th| and |io| are
composed, yielding |th|.
%format io- = "\F{\upiota\fatsemi}"
%format -io = "\F{\fatsemi\upiota}"
%format _-io = "\F{" _ "}\!" -io
%format io~ = "\F{\upiota\fatsemi\!\!\sim}"
%format ~io = "\F{\sim\!\!\fatsemi\upiota}"
%format _~io = "\F{" _ "}\!" -io
%if False
\begin{code}
module _ {X : Set} where
\end{code}
%endif
\begin{code}
  io-   : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> (CTri io th th)
  io- (th -^ x)  = io- th -^ x
  io- (th -, x)  = io- th -, x
  io- []         = []

  infixl 30 _-io
  _-io  : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> (CTri th io th)
  (th -^ x)  -io = th -io -^, x
  (th -, x)  -io = th -io -, x
  []         -io = []
\end{code}
We may readily extract identity absorption laws in equational form.
\begin{code}
  io~   : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> io -<= th ~ th
  io~ th with _ , v <- io <-> th | splatrr <- v ~-~ io- th = splatr
  _~io  : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> th -<= io ~ th
  th ~io with _ , v <- th <-> io | splatrr <- v ~-~ th -io = splatr
\end{code}
\end{lemma}

%format ga0 = ga sb0
%format ga1 = ga sb1
%format ga2 = ga sb2
%format ga3 = ga sb3
%format th01 = th sb01
%format th12 = th sb12
%format th23 = th sb23
%format th02 = th sb02
%format th13 = th sb13
%format th03 = th sb03
Framing the associativity of composition in terms of triangles gives us a choice.
When three arrows compose in sequence, they generate three more, together with four
triangles.
\[\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar@@{.>}[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar@@{.>}[uuurr]_{|th02|}
        \ar@@{.>}[uuuu]^{|th03|} & &  \\
}\]
Associativity amounts to the assertion that, given any two of the three composite
arrows, with the two triangles they generate, the whole diagram can be recovered.
All three results are useful, and they are interderivable, but one must be
proven by induction --- not on \emph{thinnings} but on \emph{triangles}.

\begin{lemma}[Associativity (03)]
\[\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar[uuurr]_{|th02|}
        \ar@@{.>}[uuuu]^{|th03|} & &  \\
}\]
%format assoc03 = "\F{assoc03}"
\begin{code}
  assoc03 : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{th01 : ga0 <= ga1}{th02 : ga0 <= ga2}{th13 : ga1 <= ga3}{th23 : ga2 <= ga3}  -> {->-}  <(CTS2 th01 th02) :* (CTS1 th23 th13)> 
           ->                                                                                                                            <(CTS3 th01 th13) :* (CTS3 th02 th23)>
  assoc03 (v        & w -^ x)   with v' & w' <- assoc03 (v & w)  = v' -^ x   & w' -^ x
  assoc03 (v -^ x   & w -^, x)  with v' & w' <- assoc03 (v & w)  = v' -^ x   & w' -^, x
  assoc03 (v -^, x  & w -, x)   with v' & w' <- assoc03 (v & w)  = v' -^, x  & w' -^, x
  assoc03 (v -, x   & w -, x)   with v' & w' <- assoc03 (v & w)  = v' -, x   & w' -, x
  assoc03 ([]       & [])                                        = []        & []
\end{code}
There are three step cases for an inserted |x|, covering the three stages in the
sequence where it can have been inserted. There is one step case for a copied |x|,
which must have be copied in all three stages.

The more familiar equational form of associativity follows by triangulation.
%format pp = "^{\V{\prime}}"
%format assoc = "\F{assoc}"
%format v012 = v sb012
%format v013 = v sb013
%format v023 = v sb023
%format v123 = v sb123
%format v013' = v013 pp
%format v023' = v023 pp
\begin{code}
  assoc  : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{->-}  (th01 : ga0 <= ga1)(th12 : ga1 <= ga2)(th23 : ga2 <= ga3)
         ->                                            th01 -<= (th12 -<= th23) ~ (th01 -<= th12) -<= th23
  assoc th01 th12 th23 with  th13  , v123 <- th12 <-> th23  | th02  , v012 <- th01 <-> th12  |
                             _     , v013 <- th01 <-> th13  | _     , v023 <- th02 <-> th23  |
    v013' & v023' <- assoc03 (v012 & v123) | splatrr,rr <- v013 ~-~ v013' , v023 ~-~ v023' = splatr
\end{code}
\end{lemma}

We may also derive the other two forms of diagrammatic composition.

\begin{lemma}[Associativity (02, 13)]
\[\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar@@{.>}[uuurr]_{|th02|}
        \ar[uuuu]^{|th03|} & &  \\
}
\qquad\qquad\qquad
\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar@@{.>}[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar[uuurr]_{|th02|}
        \ar[uuuu]^{|th03|} & &  \\
}\]
%format assoc02 = "\F{assoc02}"
%format assoc13 = "\F{assoc13}"
\begin{code}
  assoc02 : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{th01 : ga0 <= ga1}{th03 : ga0 <= ga3}{th12 : ga1 <= ga2}{th23 : ga2 <= ga3}  -> {->-}  <(CTS2 th01 th03) :* (CTS3 th12 th23)> 
           ->                                                                                                                            <(CTS3 th01 th12) :* (CTS1 th23 th03)>
  assoc02 {th01 = th01}{th12 = th12} (v013 & v123) with th02 , v012 <- th01 <-> th12 |
    v013' & v023 <- assoc03 (v012 & v123) | splatrr <- v013 ~-~ v013'
    = v012 & v023

  assoc13 : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{th01 : ga0 <= ga1}{th03 : ga0 <= ga3}{th12 : ga1 <= ga2}{th23 : ga2 <= ga3}  -> {->-}  <(CTS3 th01 th12) :* (CTS1 th23 th03)> 
           ->                                                                                                                            <(CTS2 th01 th03) :* (CTS3 th12 th23)>
  assoc13 {th12 = th12}{th23 = th23} (v012 & v023) with th13 , v123 <- th12 <-> th23 |
    v013 & v023' <- assoc03 (v012 & v123) | splatrr <- v023 ~-~ v023'
    = v013 & v123
\end{code}
That is, we construct the missing arrow and one of the triangles by composition.
The |assoc03| lemma gives us the other triangle we want and a duplicate of one we
already have. Contracting the duplication makes the triangles we want fit together.
\end{lemma}

We should now able to construct the category of thinnings, if only we knew
what it might mean to construct a category \emph{in type theory}. That is when our troubles
really begin.


\section{Type Theorists Worry About Equality}

An ingenue (or very sophisticated troll) once wrote to some mathematical mailing list
asking whether category theory and type theory were the same. Some category theorists
answered vaguely in the positive, at which point the type theorists accused them of
insufficiently interrogating the meaning of `the same'. The title of this section is
tantamount to a definition of the discipline, especially if you come from the school
which takes the classification of a thing to be the diagonal of the classified
partial equivalence relation which says when two things are the same.

Informally, a category is given by
\begin{enumerate}
\item some notion of \emph{objects};
\item for every pair of objects, \emph{source} and \emph{target},
  some notion of \emph{arrows} from source to target;
\item for each object, an \emph{identity} arrow from that object to itself;
\item for each pair of arrows which meet in the middle, a \emph{composite} arrow from
  the source of the first to the target of the second;
\item ensuring that composition absorbs identity and associates, i.e., that some
  equations between arrows hold.
\end{enumerate}

For thinnings, our objects are scopes and |<=| tells us what the arrows are. We have
candidates for identity and composition. We can take the same view of types and
functions: |Set| gives our objects, |->| our arrows, and we have the identity function
and function composition.

But any type theorist will ask, or rather will \emph{be asked} by their equipment,
`What is the status of equations between arrows?'. For thinnings, which are first
order inductive data structures (indeed, bit vectors), the intensional |~| should
suffice; for functions, |~| is dangerously restrictive, identifying only functions
with the same \emph{implementation}, up to definitional equality. Any workable
notion of category within type theory has to negotiate this distinction, which is
waved away in everyday mathematical practice.

We have three options:

\begin{enumerate}
\item \emph{Worry About Equality.}~ Work to replace intensional |~| by something which
  better reflects mathematical intuition. That is the work of many lifetimes,
  mine included, and it is beginning to pay off. Observational Type Theory gave
  a good answer to when values are equal, but not such a good answer to when types are
  equal. (It was never the basis of a usable implementation, a fact for which I
  bear some blame.) Homotopy Type Theory gives a better answer, and in its Cubical
  variant, is beginning to materialise. This is the best option, if you have
  patience.
\item \emph{Tell Lies.}~ Postulate that |~| has the properties we wish it had, e.g.
  that pointwise equal functions are equal. Get on with exploring the important ideas.
  Unfortunately, the computational properties of postulates frustrate the execution of
  actual, if sophisticated, programs when proofs of equations are used to transport
  actual values between merely provably equal types. None the less, this is the best
  option, if you have undergraduates.
\item \emph{Tell Weaker Truths.}~ Arrange to work up to |~| when you
  can (e.g., with thinnings) and to weaker notions (e.g., pointwise equality for
  functions) when you cannot. This is the best option, if you are in a hurry.
\end{enumerate}

My head is with option 1, my heart is with option 2, but my entire digestive system is
with option 3, so that is how I shall proceed in this paper.

The plan, which is far from original, is to work with setoids of arrows,
carefully managing the appropriate notion of equivalence on a case-by-case basis.
A \emph{setoid} is a set equipped with an \emph{arbitrary} equivalence relation.

%format Setoid = "\D{Setoid}"
%format El = "\F{El}"
%format Eq = "\F{Eq}"
%format Rf = "\F{Rf}"
%format Sy = "\F{Sy}"
%format Tr = "\F{Tr}"
%format lsuc = "\D{lsuc}"
\begin{definition}[Setoid]
Every level of the hierarchy is equipped with a notion of |Setoid|.
\begin{code}
record Setoid l : Set (lsuc l) where
  field  El  :  Set l                                         -- |El|ements
         Eq  :  El -> El -> Set l                             -- |Eq|uivalence
         Rf  :  (x : El)      -> Eq x x                       -- \F{R}e\F{f}lexivity
         Sy  :  (x y : El)    -> Eq x y -> Eq y x             -- |Sy|mmetry
         Tr  :  (x y z : El)  -> Eq x y -> Eq y z -> Eq x z   -- |Tr|ansitivity
open Setoid
\end{code}
\end{definition}

Let us now build some tools to enable the construction of some |Setoid|s that we
can use to specify arrows in categories and what we expect to be able to prove
about them.

\begin{definition}[Intensional |Setoid|s]
Every |Set| gives rise to a |Setoid| whose equivalence is given by |~|.
%format IN = "\F{\mathrm{IN}}"
\begin{code}
IN : {-<-} forall {l} -> {->-} Set l -> Setoid l
El  (IN X) =   X
Eq  (IN X) =   _~_
Rf  (IN X) x               = r~
Sy  (IN X) x  y    r~      = r~
Tr  (IN X) x  y z  r~  r~  = r~
\end{code}
\end{definition}

\begin{definition}[Comprehension |Setoid|s]
Fix levels |k| and |l|.
\begin{code}
module _ {k l : Level} where
\end{code}
From any |Setoid k|, we can construct a further |Setoid| by \emph{proof irrelevant}
comprehension on its elements with respect to a predicate in |l|.
%format || = "\F{\parallel}"
%format _||_ = "\F{" _ "}\!" || "\!\F{" _ "}"
%format PI = "\F{\mathrm{PI}}"
%format IM = "\F{\mathrm{IM}}"
%format SG = "\F{\mathrm{SG}}"
%format s0 = s sb0
%format s1 = s sb1
%format t0 = t sb0
%format t1 = t sb1
%format t2 = t sb2
%format t01 = t sb01
%format t12 = t sb12
\begin{code}
  _||_ : (T : Setoid k)(P : El T -> Set l) -> Setoid (k \-/ l)
  El  (T || P) = [* x :: El T ]* P x
  Eq  (T || P) (t0 , _) (t1 , _) = Eq T t0 t1 * One {l}
  Rf  (T || P) (t , _)                                           = Rf T t , <>
  Sy  (T || P) (t0 , _) (t1 , _) (t01 , <>)                      = Sy T t0 t1 t01 , <>
  Tr  (T || P) (t0 , _) (t1 , _) (t2 , _) (t01 , <>) (t12 , <>)  = Tr T t0 t1 t2 t01 t12 , <> 
\end{code}
\end{definition}

The |Eq| for comprehensions demands an element of the unit type instead
of a proof that the proofs of |P| are equal: this is both a vestigial
marker of some information that has been thrown away, and the means to
bully Agda into accepting that the |Eq| type is at level |k \-/ l| rather
than level |k|.

\begin{definition}[Pointwise |Setoid|s]
Fix a |Set| |S| and a family of |Setoid|s |T|.
\begin{code}
module _ {k l}(S : Set k)(T : S -> Setoid l) where
\end{code}
We may then construct |Setoid|s which lift |T| pointwise by quantification
(universal or existential over |S|.
\begin{code}
  PI : Setoid (k \-/ l)
  El  PI     = (s : S) -> El (T s)             -- explicit universal quantification
  Eq  PI f g = (s : S) -> Eq (T s) (f s) (g s)
  Rf  PI f s          = Rf (T s) (f s)
  Sy  PI f g q s      = Sy (T s) (f s) (g s) (q s)
  Tr  PI f g h p q s  = Tr (T s) (f s) (g s) (h s) (p s) (q s)

  IM : Setoid (k \-/ l)
  El  IM     = {s : S} -> El (T s)             -- implicit universal quantification
  Eq  IM f g = (s : S) -> Eq (T s) (f {s}) (g {s})
  Rf  IM f s          = Rf (T s) f
  Sy  IM f g q s      = Sy (T s) f g (q s)
  Tr  IM f g h p q s  = Tr (T s) f g h (p s) (q s)

  SG : Setoid (k \-/ l)
  El  SG = [* s :: S ]* El (T s)               -- existential quantification
  Eq  SG (s0 , t0) (s1 , t1) = Sg (s0 ~ s1) \ { r~ -> Eq (T s0) t0 t1 }
  Rf  SG (s , t)                                               = r~ , Rf (T s) t
  Sy  SG (s , t0) (.s , t1) (r~ , t01)                         = r~ , Sy (T s) t0 t1 t01
  Tr  SG (s , t0) (.s , t1) (.s , t2)   (r~ , t01) (r~ , t12)  = r~ , Tr (T s) t0 t1 t2 t01 t12
\end{code}
\end{definition}

\begin{craft}[Green Things in Blue Packaging]
I anticipate that we shall need to construct explanations which look like
equational proofs, but are constructed within the equivalence of a known
|Setoid|. I therefore introduce a type constructor whose entire purpose is
to fix the |Setoid| at work. There is no general way to infer the setoid
|X| from a type which is known to be |Eq X x y|, so the craft lies in ensuring
that we never forget which |Setoid| we work in.
%
%format :> = "\mathrel{\D{\ni}}"
%format ~~ = "\mathrel{\D{\approx}}"
%format _:>_~~_ = "\D{" _ "}\!" :> "\!\D{" _ "}\!" ~~ "\!\D{" _ "}"
%format eq = "\C{eq}"
%format qe = "\F{qe}"
%format ~[ = "\F{\approx\!\!\![}"
%format >~ = "\F{\rangle\!\!\!\approx}"
%format ~< = "\F{\approx\!\!\!\langle}"
%format ]~ = "\F{]\!\!\!\approx}"
%format [SQED] = "\F{\square}"
%format RfX = "\F{RfX}"
%format SyX = "\F{SyX}"
%format TrX = "\F{TrX}"
%format _~[_>~_ = _ ~[ _ >~ _
%format _~<_]~_ = _ ~< _ ]~ _
%format _[SQED] = _ [SQED]
%format rS = "\F{r\!\!\approx}"
%format qprf = "\F{qprf}"
%
\begin{code}
record _:>_~~_ {l}(X : Setoid l)(x y : El X) : Set l where
  constructor  eq
  field        qe : Eq X x y
open _:>_~~_ public
\end{code}
When we formulate categorical laws, we shall use this wrapped version.
\end{craft}

At last, we are ready to say what a category might be.


\section{Categories, Type Theoretically}

What follows is far from perfect. The best that can be said is that it is an
effective pragmatic compromise. Neither is it an unusual recipe. I labour the
point only to teach the craft of the cooking.

A category will have a |Set| of objects and, indexed by source and target objects,
a |Setoid| of arrows.

But there's another catch: type theoretic level. There is no
good reason to believe that the level objects live on is in any way related to the
the level that arrows live on. Agda is particularly bad at supporting
\emph{cumulativity} --- implicit upward flow between levels --- and by `bad', I mean
it just does not. (Coq by contrast, is rather good at it.) Agda forces one to use
level polymorphism instead of cumulativity. The two are poor stablemates, but they
have backed the wrong horse. In the now, the pragmatic policy is to keep the levels
of objects and arrows separate.

%format Level = "\D{Level}"
%format Cat = "\D{Cat}"
%format Obj = "\F{Obj}"
%format Arr = "\F{Arr}"
%format ~> = "\F{\vartriangleright\!}"
%format _~>_ = "\F{" _ "\!}" ~> "\F{\!" _ "}"
%format _~~_ = "\D{" _ "\!}" ~~ "\D{\!" _ "}"
%format id = "\F{\upiota}"
%format - = "\F{\fatsemi}"
%format _-_ = "\F{" _ "\!}" - "\F{\!" _ "}"
%format coex = "\F{coex}"
%format idco = "\F{idco}"
%format coid = "\F{coid}"
%format coco = "\F{coco}"
\begin{definition}[|Cat|egory]
Fix |k|, the level of objects, and |l|, the level of arrows.
%if False
\begin{code}
module _ (k l : Level) where  -- fix |k|, the level of objects,
                              -- and |l|, the level of arrows
\end{code}
%endif

We may then define a notion of |Cat|egory.
\begin{code}
  record Cat : Set (lsuc (k \-/ l)) where
    -- We have a |Set| of |Obj|ects, and a family of |Setoid|s of |Arr|ows.
    field      Obj   :  Set k
               Arr   :  Obj -> Obj -> Setoid l
               -- Agda allows one to pause between |field|s to make \emph{definitions}\ldots
    _~>_ : Obj -> Obj -> Set l
    S ~> T = El (Arr S T)
               -- \ldots and then resume requesting |field|s.
    -- We have identity and composition.
    field      id    :  {-<-}{T : Obj} -> {->-}      T ~> T
               _-_   :  {-<-}{R S T : Obj} -> {->-}  R ~> S -> S ~> T -> R ~> T
    -- Locally define equality of arrows\ldots
    _~~_ : {S T : Obj}(f g : S ~> T) -> Set l
    _~~_ {S}{T} f g = Arr S T :> f ~~ g
    -- \ldots then require the laws.
    field      coex  :  {-<-}{R S T : Obj}{f f' : R ~> S}{g g' : S ~> T} -> {->-}  f ~~ f' -> g ~~ g' -> (f - g) ~~ (f' - g')
               idco  :  {-<-}{S T : Obj}{->-}(f : S ~> T) ->                              (id - f)       ~~  f
               coid  :  {-<-}{S T : Obj}{->-}(f : S ~> T) ->                              (f - id)       ~~  f
               coco  :  {-<-}{R S T U : Obj}{->-}(f : R ~> S)(g : S ~> T)(h : T ~> U) ->  (f - (g - h))  ~~  ((f - g) - h)
\end{code}
Note the inevitable necessity of |coex|, the explicit witness that composition
respects the weak notion of equivalence given by |~~|: let us ensure that this
proof is always trivial.
\end{definition}

As a warm-up, let us construct the category of sets and
functions-up-to-pointwise-equality.

\begin{definition}[Pointwise Set]
Every level {l} of the type theoretic hierarchy has a category of sets and
functions, considered up to pointwise equality. The objects in the category
are large, but the arrows are small.
%format SET = "\F{SET}"
\begin{code}
module _ (l : Level) where
  open Cat

  SET : Cat (lsuc l) l
  Obj  SET = Set l
  Arr  SET S T = PI S \ _ -> IN T
  id   SET x      = x
  _-_  SET f g x  = g (f x)
  qe (coex SET {f = f} (eq qf) (eq qg)) x  with f x  | qf x
  ...                                      | _       | r~ = qg _
  qe (idco SET f)      x = r~
  qe (coid SET f)      x = r~
  qe (coco SET f g h)  x = r~
\end{code}
\end{definition}
When giving the extensionality witness for composition, we know only that
its arguments agree pointwise. Fortunately for us, the definition of
composition uses its arguments by invoking them at specific points.

\begin{definition}[Discrete Category]
Every |Set| induces a \emph{discrete category} with its elements for objects
and only identity arrows, given by intensional equality.
%format DISCRETE = "\F{DISCRETE}"
%format splatvr = contraction
%format splateqrv = contraction
%if False
\begin{code}
pattern splatvr = <> , r~
pattern splateqrv = eq (r~ , <>)
module _ {l : Level} where
  open Cat
\end{code}
%endif
\begin{code}
  DISCRETE : (X : Set l) -> Cat l l
  Obj   (DISCRETE X)                          = X
  Arr   (DISCRETE X) x y                      = IN (One {l}) || \ _ -> x ~ y
  id    (DISCRETE X)                          = splatvr
  _-_   (DISCRETE X) splatvr splatvr          = splatvr
  coex  (DISCRETE X) splateqrv splateqrv      = splateqrv
  idco  (DISCRETE X) splatvr                  = splateqrv
  coid  (DISCRETE X) splatvr                  = splateqrv
  coco  (DISCRETE X) splatvr splatvr splatvr  = splateqrv
\end{code}
I make the arrows carry \emph{trivial} information, subject to the \emph{condition}
that source and target are equal. I am therefore not obliged to reason about
equality between equality proofs.
\end{definition}


\begin{code}
module _ {l}{X : Setoid l} where
  private RfX = Rf X ; SyX = Sy X ; TrX = Tr X

  infixr 5 _~[_>~_ _~<_]~_
  infixr 6 _[SQED]

  _~[_>~_ : {-<-} {y z : El X} -> {->-} forall x -> X :> x ~~ y -> X :> y ~~ z -> X :> x ~~ z
  x ~[ eq q >~ eq q' = eq (TrX _ _ _ q q')
  
  _~<_]~_ : {-<-} {y z : El X} -> {->-} forall x -> X :> y ~~ x -> X :> y ~~ z -> X :> x ~~ z
  x ~< eq q ]~ eq q' = eq (TrX _ _ _ (SyX _ _ q) q')

  _[SQED] : (x : El X) -> X :> x ~~ x
  x [SQED] = eq (RfX x)
  
  rS : {-<-} forall {x : El X} -> {->-}  X :> x ~~ x
  rS {x} = eq (RfX x)

qprf : {-<-} forall {l} -> {->-} (X : Setoid l){x y : El X} -> X :> x ~~ y -> Eq X x y
qprf X = qe
\end{code}

\bibliographystyle{plain}
\bibliography{EGTBS}

\end{document}
