\section{Natural Transformations --- Functors as Objects}

%if False
\begin{code}
module Natural where

open import Agda.Primitive renaming (_⊔_ to _\-/_)

open import DeBruijn
open import Thinnings
open import Slime
open import Worry
open import Categories
open import Functors

open Cat
\end{code}
%endif

We have seen functors as arrows in |CAT|, but they are also objects in
\emph{functor categories}, whose arrows are \emph{natural transformations}:
families of arrows in the target category which operate \emph{uniformly}.
Let us proceed directly.

\begin{lemma}[Functor Category]
Fix source category |C| and target category |D|, irrespective of size.
\begin{code}
module _ {k l k' l' : Level}(C : Cat k l)(D : Cat k' l') where
  private module C = Cat C ; module D = Cat D
\end{code}
  Functors from |C| to |D| are the objects of a category with the following notion
  of arrow.
%format => = "\F{\Rightarrow}"
%format _=>_ = "\F{" _ "\!}" => "\F{\!" _ "}"
\begin{code}
  _=>_ : Cat (k \-/ l \-/ k' \-/ l') (k \-/ l \-/ l')
  Obj  _=>_ = C -F> D
  Arr  _=>_ F G = 
    (IM C.Obj \ X -> D.Arr (Map F X) (Map G X))
    || \ n ->  {S T : C.Obj}(f : S C.~> T) -> 
               (map F f D.- n {T}) D.~~ (n {S} D.- map G f)
\end{code}
What are these arrows? They are families of arrows in |D| indexed by objects in
|C|: for each |X|, we get a |D| arrow, |n {X}| from |F X| to |G X|. However, they are
subject to a \emph{naturality} condition.
\[\xymatrix{
   |F X| \ar[r]^{|n {X}|}\ar[d]_{|Fm f|} & |G X| \ar[d]^{|Gm f|} \\
   |F Y| \ar[r]^{|n {Y}|} & |G Y|
}\]
That is, |n| turns |F|-shaped things into |G|-shaped things, without regard to
contents.
\end{lemma}

Let us now construct the category.
\begin{enumerate}
\item identity, and the proof that it is natural
\begin{code}
  id _=>_ {F}
    =  D.id , \ f ->
         map F f D.- D.id      ~[ D.coid _ >~
         map F f               ~< D.idco _ ]~
         (D.id D.- map F f)    ~[SQED]
\end{code}
\item composition, and the proof that it preserves naturality
\begin{code}
  _-_ _=>_ {F}{G}{H} (n , na) (p , pa) =  n D.- p , \ f ->
         map F f D.- (n D.- p)      ~[ D.coco _ _ _ >~
         (map F f D.- n) D.- p      ~[ D.coex (na f) rS >~
         (n D.- map G f) D.- p      ~< D.coco _ _ _ ]~
         n D.- (map G f D.- p)      ~[ D.coex rS (pa f) >~
         n D.- (p D.- map H f)      ~[ D.coco _ _ _ >~
         (n D.- p) D.- map H f      ~[SQED]
\end{code}
\item laws --- inherited pointwise from |D|
\begin{code}
  coex _=>_ (eq (nq , <>)) (eq (pq , <>)) =
    eq ((\ X -> qe (D.coex (eq (nq X)) (eq (pq X)))) , <>)
  idco _=>_ _      = eq ((\ _ -> qe (D.idco _)) , <>)
  coid _=>_ _      = eq ((\ _ -> qe (D.coid _)) , <>)
  coco _=>_ _ _ _  = eq ((\ _ -> qe (D.coco _ _ _)) , <>)
\end{code}
\end{enumerate}

Natural transformations are indexed families of functions. It help to
introduce notation for working with the latter.
Let us do for functions what |:*| and |<_>| do for pairs.
%format -:> = "\mathrel{\D{\dot{\to}}}"
%format _-:>_ = "\D{" _ "\!}" -:> "\D{\!" _ "}"
%format [ = "\D{[}"
%format ] = "\D{]}"
%format [_] = [ "\D{\!" _ "\!}" ]
Firstly, we lift the function type pointwise.
\begin{code}
_-:>_ : {-<-}forall {k l}{->-}{S : Set k}(T U : S -> Set l) -> (S -> Set l)
(T -:> U) s = T s -> U s
\end{code}
Secondly, we introduce the `necessarily' operator, indicating that a
predicate holds for its entire domain.
\begin{code}
[_] : {-<-}forall {k l}{->-}{S : Set k}(T : S -> Set l) -> Set (k \-/ l)
[ T ] = forall {s} -> T s
\end{code}
Together, we obtain |[ T -:> U ]| for an indexed family of functions.

Now, with this apparatus in place, let us revisit the |<?| operator,
which is natural with respect to the type of values being stored in
|Env|ironments.

\begin{lemma}[Natural Selection]
|Env| extends to a functor between functor categories as follows.
%format ENV = "\F{ENV}"
\begin{spec}
ENV : {-<-}{X : Set} ->{->-} (DISCRETE X => SET lzero) -F> (OP (THIN X) => SET lzero)
fst (nuf ENV) V = SELECT (Map V)
\end{spec}
\end{lemma}
In order to prove this lemma, we must program to its specification.
After unwrapping the setoid packaging, we find we must deliver an
arrow action which commutes with selection.
%format env = "\F{env}"
%format na<? = "\F{na}\!" <?
\begin{code}
env : {-<-}forall {X}{V W : X -> Set} -> {->-} [ V -:> W ] -> [ Env V -:> Env W ]
env f []         = []
env f (vz -, v)  = env f vz -, f v

na<? : {-<-}forall {X : Set}{V W}{ga de : Bwd X}{->-}  (f : [ V -:> W ])(th : ga <= de)(vz : Env V de) ->
                                                       env f (th <? vz) ~ th <? env f vz
na<? f (th -^ x)  (vz -, v) rewrite na<? f th vz  = r~
na<? f (th -, x)  (vz -, v) rewrite na<? f th vz  = r~
na<? f []         []                              = r~
\end{code}

Of course, we must also ensure that |env| is extensional and respects identity
and composition.
%format envex = "\F{envex}"
%format envid = "\F{envid}"
%format envco = "\F{envco}"
%format V0 = V sb0
%format V1 = V sb1
%format V2 = V sb2
\begin{code}
envex  : {-<-}forall {X}{V W : X -> Set}{f g : [ V -:> W ]}{ga : Bwd X} -> {->-}((x : X)(v : V x) -> f v ~ g v) -> (vz : Env V ga)
       -> env f vz ~ env g vz
envid  : {-<-}forall {X}{V : X -> Set}{ga : Bwd X}{->-}(vz : Env V ga)
       -> env (\ x -> x) vz ~ vz
envco  : {-<-}forall {X}{V0 V1 V2 : X -> Set}{->-}(f : [ V0 -:> V1 ])(g : [ V1 -:> V2 ]){ga}(vz : Env V0 ga)
       -> env (\ x -> g (f x)) vz ~ env g (env f vz)
\end{code}
These are routine functional inductions.
%if False
\begin{code}
envex q []                                    = r~
envex q (vz -, v) rewrite envex q vz | q _ v  = r~

envid []                          = r~
envid (vz -, v) rewrite envid vz  = r~

envco f g [] = r~
envco f g (vz -, v) rewrite envco f g vz = r~

ENV : {X : Set} -> (DISCRETE X => SET lzero) -F> (OP (THIN X) => SET lzero)
fst (nuf ENV) V = SELECT (Map V)
\end{code}
%endif
The whole jigsaw comes together, as follows:
\begin{code}
snd (nuf ENV)
  =  (\ { (f , _) -> env f , \ th -> eq (na<? f th) })
  ,  (\ { (eq (q , <>)) -> eq ((\ ga -> envex q) , <>) })
  ,  eq ((\ ga -> envid) , <>)
  ,  \ { (f , _) (g , _) -> eq ((\ ga -> envco f g) , <>) }
\end{code}

