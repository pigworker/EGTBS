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
\usepackage{stmaryrd}
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
module extended where
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

%include DeBruijn.hide.lagda
%if False
\begin{code}
open import DeBruijn
\end{code}
%endif

%include Thinnings.hide.lagda
%if False
\begin{code}
open import Thinnings
\end{code}
%endif

%include Slime.hide.lagda
%if False
\begin{code}
open import Slime
\end{code}
%endif

%include Worry.hide.lagda
%if False
\begin{code}
open import Worry
\end{code}
%endif

%include Categories.hide.lagda
%if False
\begin{code}
open import Categories
\end{code}
%endif

%include Functors.hide.lagda
%if False
\begin{code}
open import Functors
\end{code}
%endif

%include Natural.hide.lagda
%if False
\begin{code}
open import Natural
\end{code}
%endif


\bibliographystyle{plain}
\bibliography{EGTBS}

\end{document}
