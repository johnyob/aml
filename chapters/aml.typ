#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

// HACK to get thm to left align
#show: thmrules

In this section we summarise the syntax and typing rules of #aml (Ambivalent ML), a conservative extension of the #ml calculus with _scoped ambivalent types_ ($[Psi] tau$) and a type-level equality type ($tau = tau'$).

_Expressions_. The syntax of expressions is as follows:
#syntax(
  syntax-rule(
    name: [Expressions],
    $e in Exp ::= &x | efun x -> e | e space e \
      | &elet x = e ein e | efun (etype alpha) -> e | (e : tau) \
      | &erefl | ematch (e : tau = tau) ewith erefl -> e$,
  ),
)

#aml extends #ml expressions, variables, functions and let expressions are standard. #aml introduces an explicit universal quantifier $efun (etype alpha) -> e$, equivalent to System #textsf("F")'s $Lambda alpha. e$. The constructor $erefl$ has the type $tau = tau$. The $ematch (e : tau_1 = tau_2) ewith erefl -> e'$ construct introduces the type-level equality in $e'$ as a _local constraint_ using the proof $e$.


_Notation_. We write $overline(e)$ for a (possible empty) set of elements ${e_1, ..., e_n}$ and a (possibly empty) sequence $e_1, ..., e_n$. The interpretation of whether $overline(e)$ is a set or a sequence is often implicit. We write $overline(e_1) disjoint overline(e_2)$ as a shorthand for when $overline(e_1) sect overline(e_2) = emptyset$. We write $overline(e_1), overline(e_2)$ as the union or concatenation (depending on the interpretation) of $overline(e_1)$ and $overline(e_2)$. We often write $e$ for the singleton set (or sequence).

_Types_. The syntax of types is as follows:
#comment[TODO: Align all syntax]
#syntax(
  horizontal-spacing: 1.25cm,
  syntax-rule(name: [Type Variables], $alpha, beta, gamma, scopev, rho.alt in varset(Ty)$),
  syntax-rule(name: [Equation Names], $eqname in varset(EqName)$),
  syntax-rule(name: [Type Constructors], $tformer in TyCon ::= dot arrow dot | dot = dot | tunit$),
  syntax-rule(name: [Types], $tau^kappa in Ty ::= alpha^kappa | overline(tau^ty) tformer | [tau^scope] tau | dot^scope | tau^scope, eqname$),
  syntax-rule(name: [Type Schemes], $sigma in Scm ::= tau | tforall(alpha :: kappa) sigma $),
  syntax-rule(name: [Kinds], $kappa in Kind ::= ty | scope$),
  syntax-rule(name: [Flexibility], $f ::= fflex | frigid$),
  syntax-rule(
    name: [Contexts],
    $Gamma in Ctx ::= &dot | Gamma, alpha^f :: kappa | Gamma, eqname : tau = tau | Gamma, x: sigma$,
  ),
)

// Kinds
Types $tau^kappa$ are _kinded_, where $kappa$ is the kind of a type $tau$, denoted by the superscript. We have the usual kind for types ($ty$), but also kinds for _scopes_ ($scope$). 
Often the kind of a type is apparent or not relevant and most of the time we will denote the kind to reduce clutter, writing $tau$ for types and $Psi$ for scopes. For clarity, we use $alpha, beta, gamma$ to denote _type variables_ and $scopev, rho.alt$ for _scope variables_. 

// Types
Types consist of type variables ($alpha$) and type constructors ($tformer$). Type constructors include functions ($arrow$), base types (such as $tunit$), and the equality withness type ($=$).
Intuiviely, a _scoped ambivalent type_ is a set of provably equivalent types. Under our equivalece relation, introduced later, $[Psi]tau$ is equivalent to a set of types $[Psi]tau'$
where $tau$ and $tau'$ are provably equal using the equations in $Psi$. An ambivalent type is only _coherent_ (in the context $Gamma$) if the equations in $Psi$ are in $Gamma$. Otherwise, the scope is said to have escaped the context.

// Scopes
A scope is defined by a _row_ of equation names. An scope is either empty $dot$, a polymorphic scope variable $scopev$, or an extension of a scope $Psi$ with an equation $eqname$, written as $Psi, eqname$. Unlike many other applications of row polymorphism, we _do_ allow duplicate equation names, meaning that $eqname, eqname$ is _well-formed_ (though not equal to the scope $eqname$). However, our use of rows is primarily to represent sets of equations and ensure _coherence_, so these duplicates do not pose a problem.  

// Schemes
Polymorphic types are defined by _type schemes_ in a mostly typical #ml fashion, generalzing over zero or more variables. However, we extend the notion of polymorphism to also quantify over _scope variables_ as well, introducing a form of _scope polymorphism_.

// Contexts
Contexts bind term variables to type schemes, introduce (polymorphic) type and scope variables, and store (named) type equations $eqname: tau = tau'$. Each type variable is associated with a _flexibility_ $f$ which can either be _rigid_ ($frigid$) or _flexible_ ($fflex$), indicating whether the variable was introduced by an explicit $efun (etype alpha) -> e$ quantifier or implicitly due to let-polymorphism.
Contexts are ordered and duplicates are disallowed. We write $Gamma, Gamma'$ for the concatenation of two contexts (assuming disjointness holds). We write $dom(Gamma)$ for the _domain_ of the context, which informally represents the set of type and scope variables, term variables and equation names. We often write $overline(e) disjoint Gamma$ as a shorthand for $overline(e) disjoint dom(Gamma)$.

We assume types, scopes, and type schemes are equivalent modulo $alpha$-renaming.

The definition for the set of free variables on types and schemes is standard.

$
  fv (alpha) &= { alpha } &&& fv (dot) &= emptyset \
  fv (overline(tau) tformer) &= union.big_i fv (tau_i) &&& fv (Psi, eqname) &= fv (Psi) \
  fv ([Psi] tau) &= fv (Psi) union fv (tau) &#h(2cm)&&  fv(tforall(alpha :: kappa) sigma) &= fv(sigma) \\ { alpha } \  \
$



_Well formedness_. Well-formedness judgements for types, type schemes, and contexts ensure the soundness of scoped ambivalent types and the coherent use of variables.


#judgement-box($f_1 <= f_2$, $Gamma tack tau^kappa :: kappa space  f$, $Gamma tack sigma scm$, $Gamma ctx$)

$

  #proof-tree(
    rule(
      $f <= f$
    )
  )

  #h1 
  

  #proof-tree(
    rule(
      $frigid <= fflex$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack alpha :: kappa space f'$,
      $alpha^f :: kappa in Gamma$, 
      $f <= f'$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(tau) tformer :: ty f$,
      $forall i. space Gamma tack tau_i :: ty f$
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Gamma tack [Psi] tau :: ty fflex$,
      $Gamma tack Psi :: scope fflex$,
      $Gamma tack tau :: ty frigid$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack dot :: scope fflex$,
      $$
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Gamma tack Psi, eqname :: scope fflex$,
      $Gamma tack Psi :: scope fflex$,
      $eqname in dom(Gamma)$
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma tack tforall(alpha :: kappa) sigma scm$,
      $Gamma, alpha^fflex :: kappa tack sigma scm$,
      $alpha disjoint Gamma$
    )
  )


  #v2

  #proof-tree(
   rule(
      $dot ctx$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, alpha^f :: kappa ctx$,
      $Gamma ctx$,
      $alpha disjoint Gamma$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma, eqname: tau_1 = tau_2 ctx$,
      $Gamma ctx$,
      $Gamma tack tau_1 :: ty frigid$,
      $Gamma tack tau_2 :: ty frigid$,
      $eqname disjoint Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma, x : sigma ctx$,
      $Gamma ctx$,
      $Gamma tack sigma scm$,
      $x disjoint Gamma$
    )
  )
$

// Rigid types in well-formedness
It is interesting to note that types $tau$ _under_ a scope $Psi$ must be _rigid_. This restriction, inherited from Remy and Garrigue's [??] work on ambivalent types, simplifies our presentation and is sufficient to encode OCaml's behaviour. Flexibility of variables in the context may be weakened using the $f <= f'$ relation. We write $Gamma tack tau^kappa :: kappa$ when the flexibility doesn't matter. 

// Equivalence 
We have an equivalence relation on types, written $Gamma tack tau equiv tau'$, with the following set of axioms:
#[
  // HACK: to align these in the center while having the "if" condition to the side
  #show math.equation: set align(end)
  $
    [Psi](tau_1 -> tau_2) &equiv [Psi]tau_1 -> [Psi] tau_2 \
  [Psi](tau_1 = tau_2) &equiv [Psi]tau_1 = [Psi]tau_2 \
  // [Psi_1][Psi_2]tau &equiv [Psi_1, Psi_2]tau \
  // BUG: Should be able to use h(1fr), but this doesn't work in mathmode
  [Psi]tau_1 &equiv [Psi]tau_2 & #h(2.8cm) "if" Gamma; Psi tack tau_1 equiv tau_2  \
  [dot] tau &equiv tau
  $
]




To prove equivalences between rigid types under a scope $Psi$, we can either use equalities introduced previously in $Gamma$ and referenced in $Psi$, and the rules of symmetry, transitivity, congruence, decomposition, and distributivity. Type constructors are injective. We formalize this using the $Gamma; Psi tack tau_1 equiv tau_2$ judgement.

Our equivalence relation on types has an interesting link to _contextual modal types_. Namely we can interpret $[Psi] tau$ as a contextual modal type $square_Psi tau$.
With this view, we can see the first two equivalences as the _distributive_ axiom for modal logic.
This connection is formalized in our chapter on #xaml, the _Explicit #aml _ calculus.

#judgement-box($Gamma; Psi tack tau_1 equiv tau_2$)
$
  #proof-tree(
    rule(
      $Gamma; Psi tack tau equiv tau$,
      $Gamma tack tau :: ty frigid$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma; Psi tack tau_1 equiv tau_2$,
      $Gamma; Psi tack tau_2 equiv tau_1$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma; Psi tack tau_1 equiv tau_3$,
      $Gamma; Psi tack tau_1 equiv tau_2$,
      $Gamma; Psi tack tau_2 equiv tau_3$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma; Psi tack tau_1 equiv tau_2$,
      $eqname : tau_1 equiv tau_2 in Gamma$,
      $eqname in Psi$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma; Psi tack overline(tau_1) tformer equiv overline(tau_2) tformer$,
      $forall i. space Gamma; Psi tack tau_(1i)  equiv tau_(2i)$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma; Psi tack tau_(1i) equiv tau_(2i)$,
      $Gamma; Psi tack overline(tau_1) tformer equiv overline(tau_2) tformer$
    )
  )
$


_Typing Judgements_. #aml typing judgements have the form $Gamma tack.r e: sigma$ stating that $e$ has the type (scheme) $sigma$ in the context $Gamma$.
We assume well-formedness for contexts $Gamma ctx$. The typing rules are given below.



#let dangerous = $textsf("dangerous")$

#judgement-box($Gamma tack e : sigma$)
$
  #proof-tree(
    rule(
      $Gamma tack x : sigma$,
      $x : sigma in Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun x -> e : tau_1 -> tau_2$,
      $Gamma, x : tau_1 tack e : tau_2$,
      $Gamma tack tau_1 :: ty$
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma tack e_1 space e_2 : tau_2$,
      $Gamma tack e_1 : tau_1 -> tau_2$,
      $Gamma tack e_2 : tau_1$,
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : sigma_2$,
      $Gamma tack e_1 : sigma_1$,
      $Gamma, x : sigma_1 tack e_2 : sigma_2$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e : tforall(alpha :: kappa) sigma$,
      $Gamma, alpha^fflex :: kappa tack e : sigma$,
      $alpha disjoint Gamma$,
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun (etype alpha) -> e : tforall(alpha :: ty) sigma$,
      $Gamma, alpha^frigid :: ty tack e : sigma$,
      $alpha disjoint Gamma$,
      $alpha in.not dangerous(sigma)$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau_2$,
      $Gamma tack e : tau_1$,
      $Gamma tack tau_1 >= forall ceil(tau :: ty frigid) <= tau_2$,
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : tforall(alpha :: ty) alpha = alpha$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack () : tforall(scopev :: scope) [scopev]tunit$,
      $$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : sigma$,
      $Gamma tack e_1 : tau$,
      $Gamma tack forall ceil(tau_1 = tau_2 :: ty frigid) <= tau$,
      $eqname disjoint Gamma$,
      $Gamma, eqname : tau_1 = tau_2 tack e_2 : sigma$,
      $Gamma tack sigma scm$,
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e : sigma'$,
      $Gamma tack e : sigma$,
      $Gamma tack sigma <= sigma'$,
    )
  )
$

_Variables_. Variables $(x)$ are typed as usual. If a variable has a polymorphic type, the standard #ml instantiation rule applies. The instantiation relation $Gamma tack sigma <= sigma'$ is defined as follows:
$
  #proof-tree(
    rule(
      $Gamma tack tau <= tau'$,
      $Gamma tack tau equiv tau'$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tforall(alpha :: kappa) sigma <= sigma'$,
      $Gamma tack tau^kappa :: kappa$,
      $Gamma tack sigma[alpha := tau^kappa] <= sigma'$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack sigma <= tforall(alpha :: kappa) sigma'$,
      $Gamma, alpha^fflex :: kappa tack sigma <= sigma'$,
      $alpha disjoint Gamma$
    )
  )
$

This relation is mostly standard, adapted to account for type equivalence and scope polymorphism.
An interesting consequence of our instantiation relation is that the following rule is admissable in #aml:
$
  #proof-tree(
  rule(
    $Gamma tack e : tau'$,
    $Gamma tack e : tau$,
    $Gamma tack tau equiv tau'$
  )
)
$
This rule plays a crucial role in manipulating scopes in our typing judgements.

_Equalities_. A type-level equality may be introduced using reflexivity with the unique constructor $erefl$ of type $forall alpha. alpha = alpha$.
Pattern matching on equalities using $ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2$ can eliminate the equality witness $e_1$ of type $tau_1 = tau_2$, adding it as an implicit equality to the context $Gamma$ while type checking the body $e_2$; the witness $e_1$ must have the structure of $tau_1 = tau_2$ but may have additional scopes -- we formalize this using a _scope erasure_ function. Since the equation is only available in the scope of $e_2$, it must not be present in the return type $sigma$. We ensure this by allocating a fresh name for the equality $eqname disjoint Gamma$ and ensuring $eqname$ doesn't occur in $sigma$, this is done so by using the well-formedness judgement $Gamma tack sigma scm$.
If the return type doesn't satisfy this condition, then we say the _equation ($eqname$) has escaped its scope_.

_Annotations_. Annotations represent an explicit loss of sharing of scopes between types. This loss of sharing of scopes permits us to eliminate ambivalence in our return type, thereby preventing scope escapes. The types $tau_1, tau_2$ need not be identical to $tau$ but must instead be _consistent instances_ of $tau$. We define what is means to be a _consistent instance_ below.

// Rigid instances definition
We begin by defining a _scope insertion_ function $ceil(tau :: ty frigid)$ for rigid types, which produces a context of scope variables $cal(S)$ and a type $tau'$ with scopes inserted at _leaves_ of the type. Scopes at inner nodes can be inferred via the distributivity of scopes.

#let ceilret(a, b) = $#a triangle.r.small #b$
$
  ceil(alpha :: ty frigid) &= ceilret(scopev, [scopev]alpha) &&"fresh" scopev \
  ceil(tformer :: ty frigid) &= ceilret(scopev, [scopev]tformer) &&"fresh" scopev \
  ceil(overline(tau) tformer :: ty frigid) &= ceilret(#[$cal(S)_1, ..., cal(S)_n$], overline(tau')) tformer &#h(2cm)&"where" ceil(tau_i :: ty frigid) = ceilret(cal(S)_i, tau'_i)
$

We write $forall ceil(tau :: ty frigid)$ for $tforall(cal(S)) tau'$ where $ceil(tau :: ty frigid) = ceilret(cal(S), tau')$. This type scheme describes a set of instances that are equivalent to $tau$ after _scope erasure_. We say such instances are _consistent instances_ of $tau$. Formally, they satisfy the following:
$
  forall tau'. space Gamma tack forall ceil(tau :: ty frigid) <= tau' ==> exists tau''. space Gamma tack tau' equiv tau'' and floor(tau'' :: ty) = tau
$
where _scope erasure_, denoted $floor(tau :: ty )$, is defined as:
$
  floor(alpha :: ty ) &= alpha \
  floor(overline(tau) tformer :: ty) &= overline(floor(tau) :: ty) tformer \
  floor([Psi]tau :: ty ) &= tau
$

We use the following judgement to check whether $sigma$ is a consistent instance of $tau$:
$
  #proof-tree(
    rule(
      $Gamma tack forall ceil(tau :: ty frigid) <= sigma$,
      $Gamma tack tau :: ty frigid$,
      $Gamma tack forall ceil(tau :: ty frigid) <= sigma$
    )
  )
$
We note that $Gamma tack forall ceil(tau :: ty frigid) scm$ is implied by $Gamma tack tau :: ty frigid$, as stated in ??.
To check that both $tau_1$ and $tau_2$ are consistent instances of $tau$, we use the following shorthand $Gamma tack tau_1 >= forall ceil(tau :: ty frigid) <= tau_2$ for $Gamma tack forall ceil(tau :: ty frigid) <= tau_1$ _and_ $Gamma tack forall ceil(tau :: ty frigid) <= tau_2$.


_Functions_. Function applications $e_1 space e_2$ are standard and oblivious to scopes.
The parameter type $tau_1$ of the function $e_1$ must be equal to that of the argument $e_2$. In particular,
in the presence of scopes, if $e_1$ have the type $[Psi]tau$ where $tau$ and $Gamma; Psi tack tau equiv tau_1 -> tau_2$,
then the argument $e_2$ must have the type $[Psi]tau_1$ and the result of the application has the type $[Psi]tau_2$.
This behaviour matches the propagation of scopes for application in the following example:
```ocaml
let propagate_scope (type a) (w1 : (a, int -> int) eq) (f : a) =
  match w1 with Refl (* a = int -> int *) ->
  f 1
```
Naming `a = int -> int` as $eqname$, the result has the type $[eqname]tint$. This escapes the scope of the `match` expression, resulting in the following error (with `-principal` enabled):
```
Error: This expression has type int but an expression was expected of type 'a
       This instance of int is ambiguous:
       it would escape the scope of its equation
```

Functions $efun x -> e$ are standard, binding monomorphic types to $x$ in the body of $e$. The annotated form $efun (x : tau) -> e$ is syntactic sugar for $efun x -> elet x = (x : tau) cin e$, permitting _scope polymorphic_ types to be bound to $x$ in $e$. The use of scope polymorphism is cruicial to avoid scope escape errors when using $x$ in a context with a scope. For example, if `f` was not annotated with `(_ : a)` in the above example, then a scope escape would occur even if the return type was annotated. This is because the type of `f` would have to match $[eqname]tint$, thus leaking the equation $eqname$.


_Let Bindings and Generalization_. Let bindings $elet x = e_1 ein e_2$ assign a polymorphic type $sigma_1$ to $x$ in the scope of $e_2$. Generalizing the type of an expression is standard using _flexible_ variables is standard.

Generalization using _rigid_ variables with an explicit quantifier $efun (etype alpha) -> e$ requires the _rigid_ generalizable variable $alpha$ cannot occur in 'dangerous' positions in the type scheme. A dangerous position is one that is under a (non-trivial #footnote([All trivial scopes may be removed using equivalence])) scope. We formally define this as follows:
$
  dangerous(alpha) &= emptyset \
  dangerous(overline(tau) tformer) &= union.big_i dangerous(tau_i) \
  dangerous([Psi]tau) &= fv(tau) \
  dangerous(tforall(alpha :: kappa) sigma) &= dangerous(sigma) \\ {alpha} \
$

This is because #aml has unrestricted instaniation (and type schemes), thus permitting a generalizable rigid variable under a non-trivial scope would result in a well-formedness
issue since scoped ambivalent types $[Psi]tau$ are only well-formed if $tau$ is _rigid_.

Additionally, without this condition, a loss in principality can occur. We demonstrate this by first considering the type of `coerce`, defined below:
```ocaml
let coerce = fun (type a b) w x ->
  let x = (x : a) in
  match (w : a = b) with Refl ->
  (x : b)
```
Without the restriction on generalizable variables, the most general type that could be inferred for `coerce` is
$
  forall scopev_1, scopev_2, scopev_3, scopev_4, alpha, beta. space ([scopev_1]alpha = [scopev_2]beta) -> [scopev_3]alpha -> [scopev_4]beta
$
It is interesting to note that the type is not more general by permitting a scope on the equality since $[scopev_5]([scopev_1]alpha = [scopev_2]beta) equiv [scopev_5, scopev_1]alpha = [scopev_5, scopev_2]beta$. The issue with this inferred type is that the additional scopes lose some the sharing that Remy and Garrigue's system enforces. This results in some programs that are morally ambivalent being well-typed in our system. For example:
```ocaml
let should_not_typecheck (type a) (w : (a, int) eq) (x : a) =
  match w with Refl ->
  let y = if true then x else 0 in
  coerce Refl y
```
We note that `y` has the type $[eqname : alpha = tint]alpha$ (or $[eqname : alpha = tint]tint$), yet we can infer $tint$ or $alpha$ for the result of `should_not_typecheck`. This amounts to a loss in principality. Our notion of 'dangerous' variables encodes that in order to generalize $alpha, beta$, the type system must ensure $alpha, beta$ do not occur under scopes. With this constraint, the principal type for `coerce` is:
$
  forall alpha, beta. space (alpha = beta) -> alpha -> beta
$

#comment[TODO: Examples]

== Metatheory


We now formalize a _syntax-directed_ variant of #aml, proving soundness and completeness with respect to the #aml typing judgements. This provides invertability lemmas that are cruicial for proving that constraint generation is sound and complete with respect to #aml's typing judgements. 

We also prove other useful lemmas such as weakening, exchange, substitution, and well-formedness. 

#comment[FIXME: All of these lemmas/theorems are used exclusively on the syntax directed system. Its probably better to move the SD theorems up and these down.]

#definition[A context $Theta$ is _soft_ if it only consists of $alpha^kappa :: f$ bindings.]

#theorem("Weakening")[
  Suppose $Gamma, Theta, Delta ctx$. Then
  + If $Gamma, Delta tack tau^kappa :: kappa space f$, then $Gamma, Theta, Delta tack tau^kappa :: kappa space f$
  + If $Gamma, Delta tack tau equiv tau'$, then $Gamma, Theta, Delta tack tau equiv tau'$
  + If $Gamma, Delta tack sigma <= sigma'$, then $Gamma, Theta, Delta tack sigma <= sigma'$
  + If $Gamma, Delta tack e : sigma$, then $Gamma, Theta, Delta tack e : sigma$
]
#proof[
  By induction on the derivation. 
]

#theorem("Flexibility Weakening")[
  Suppose $Gamma ctx$ and $Gamma tack tau^kappa :: kappa space f$, then $Gamma tack tau^kappa :: kappa space f'$ where $f <= f'$.
]
#proof[
  By induction on the derivation. 
]

#theorem("Type Exchange")[
  Suppose $Theta, Delta$ are soft and $Gamma, Theta, Delta ctx$. Then
  + If $Gamma, Theta, Delta tack tau^kappa :: kappa space f$, then $Gamma, Delta, Theta tack tau^kappa :: kappa space f$. 
  + If $Gamma, Theta, Delta tack tau equiv tau'$, then $Gamma, Delta, Theta tack tau equiv tau'$
  + If $Gamma, Theta, Delta tack sigma <= sigma'$, then $Gamma, Delta, Theta tack sigma <= sigma'$
  + If $Gamma, Theta, Delta tack e : sigma$, then $Gamma, Delta, Theta tack e : sigma$
]
#proof[
  By induction on the derivation. 
]

#theorem("Type Substitution")[
  Suppose $Gamma tack tau^kappa :: kappa space f$. Then 
  + If $Gamma, alpha^f :: kappa, Delta tack tau^kappa' :: kappa' space f'$, then $Gamma, Delta[alpha := tau^kappa] tack tau^kappa'[alpha := tau^kappa] :: kappa' space f'$
  + If $Gamma, alpha^f :: kappa, Delta tack tau_1 equiv tau_2$, then $Gamma, Delta[alpha := tau^kappa] tack tau_1[alpha := tau^kappa] equiv tau_2[alpha := tau^kappa]$
  + If $Gamma, alpha^f :: kappa, Delta tack sigma <= sigma'$, then $Gamma, Delta[alpha := tau^kappa] tack sigma[alpha := tau^kappa] <= sigma'[alpha := tau^kappa]$
  + If $Gamma, alpha^f :: kappa, Delta tack e : sigma$, then $Gamma, Delta[alpha := tau^kappa] tack e[alpha := tau^kappa] : sigma[alpha := tau^kappa]$
]
#proof[
  By induction on the derivation of the substitutee. 
]


#theorem("Well-formedness Properties")[
  Suppose $Gamma ctx$. 
  + If $Gamma; Psi tack tau_1 equiv tau_2$, then $Gamma tack tau_1 :: ty frigid$ and $Gamma tack tau_2 :: ty frigid$.
  + If $Gamma tack tau_1 equiv tau_2$, then $Gamma tack tau_1 :: ty f$ and $Gamma tack tau_2 :: ty f$.
  + If $Gamma tack sigma_1 <= sigma_2$, then $Gamma tack sigma_1 scm$ and $Gamma tack sigma_2 scm$. 
  + If $Gamma tack e : sigma$, then $Gamma tack sigma scm$. 
]
#proof[
  By induction on the derivation. 
]

#theorem("Reflexivity and Transitivity of Subsumption")[
  + $Gamma tack sigma <= sigma$
  + If $Gamma tack sigma_1 <= sigma_2$ and $Gamma tack sigma_2 <= sigma_3$, then $Gamma tack sigma_1 <= sigma_3$
]
#proof[
  + By structural induction on $sigma$. 
  + By induction on the sum of the _quantifiers_ of $sigma_1, sigma_2$ and $sigma_3$. 
  #comment[I should do the proof here to be sure of the approach. ]
]

_Syntax-directed Typing Judgements._ #aml's typing judgements are not syntax-directed. It is useful to have a syntax-directed presentation to admit inversion rules solely on the structure of $e$.
This technique is entirely standard [??] and we can show the syntax-directed presentation is sound and complete with respect to the declarative rules.


#let sdtack = $scripts(tack)_textsf("SD")$
#judgement-box($Gamma sdtack e : tau$)

$
  #proof-tree(
    rule(
      $Gamma tack x : tau$,
      $x : sigma in Gamma$,
      $Gamma tack sigma <= tau$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun x -> e : tau_1 -> tau_2$,
      $Gamma, x : tau_1 tack e : tau_2$,
      $Gamma tack tau_1 :: ty$
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma tack e_1 space e_2 : tau_2$,
      $Gamma tack e_1 : tau_1 -> tau_2$,
      $Gamma tack e_2 : tau_1$,
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : tau_2$,
      $Gamma, cal(V) tack e_1 : tau_1$,
      $cal(V) disjoint Gamma$,
      $Gamma, x : forall cal(V).tau_1 tack e_2 : tau_2$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack efun (etype alpha) -> e : tau'$,
      $Gamma, alpha^frigid :: ty tack e : tau$,
      $alpha disjoint Gamma$,
      $alpha in.not dangerous(tau)$,
      $Gamma tack tforall(alpha :: ty) tau <= tau'$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau_2$,
      $Gamma tack e : tau_1$,
      $Gamma tack tau_1 >= forall ceil(tau :: ty frigid) <= tau_2$,
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : tau$,
      $Gamma tack tforall(alpha :: ty) alpha = alpha <=  tau$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack () : tau$,
      $Gamma tack tforall(scopev :: scope) [scopev]tunit <= tau$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : tau$,
      $Gamma tack e_1 : tau'$,
      $Gamma tack forall ceil(tau_1 = tau_2 :: ty frigid) <= tau'$,
      $eqname disjoint Gamma$,
      $Gamma, eqname : tau_1 = tau_2 tack e_2 : tau$,
      $Gamma tack tau ok$,
    )
  )
$


We write $cal(V)$ for a sequence of non-rigid generalizable variables $overline(alpha^fflex :: kappa)$ in the context. Rather than inlining subsumption (as is standard), we keep it explicit, 
since each inlining would produce an explicit $equiv$-equivalence, which does not improve readability. 

#lemma[_Soundness of generalization_][
  If $Gamma, cal(V) tack e : tau$ and $cal(V) disjoint Gamma$ then $Gamma tack e : tforall(cal(V)) tau$.
] <soundgen>
#proof[
  Trivial proof by induction on the cardinality of $cal(V)$.
]

#comment[TODO: Define eqs]

#lemma[
  Given $alpha in.not textsf("eqs")(Gamma)$. 

  + If $Gamma tack tau equiv tau'$ and $alpha in.not dangerous(tau')$, then $alpha in.not dangerous(tau)$
  + If $Gamma tack sigma <= sigma'$ $alpha in.not dangerous(sigma')$, then $alpha in.not dangerous(sigma)$] <dangerous-anti-monotonicity-lemma>

#proof[
  + Induction on the derivation $Gamma tack tau equiv tau'$. 
  
  + 
    We proceed by induction on the derivation of $Gamma tack sigma <= sigma'$. 
    - *Case* (Equiv)
    + Use (1)

    - *Case* ($forall$L)
    + Let us assume $Gamma tack sigma <= sigma'$. 
    + By inversion of the ($forall$L) rule, we have $sigma = tforall(beta :: kappa) sigma''$ (a), $Gamma tack tau :: kappa$ (b), and\ 
      $Gamma tack sigma''[beta := tau] <= sigma'$ (c). 
    + By induction (2.c), we have $alpha in.not dangerous(sigma''[beta := tau])$
    + By (3), we conclude $alpha in.not dangerous(sigma'')$ and $alpha in.not dangerous(tau)$. 
    + By (4), $alpha in.not dangerous(tforall(beta) sigma'')$

    - *Case* ($forall$R)
    + Let us assume $Gamma tack sigma <= sigma'$.
    + By inversion of the ($forall$R) rule, we have $sigma' = tforall(beta :: kappa) sigma''$ (a), $beta disjoint Gamma$ (b), and $Gamma, beta^fflex :: kappa tack sigma <= sigma''$ (c)
    + By definition of $dangerous$, we have $alpha in.not dangerous(sigma'')$
    + By induction (2.c), we have $alpha in.not dangerous(sigma)$
]

#theorem[_Soundness of the syntax-directed #aml typing judgements_][
  When $Gamma sdtack e : tau$ then we also have $Gamma tack e : tau$.
]

#proof[
  We proceed by structural induction on $e$.

  - *Case* $x$.
  1. Let us assume $Gamma sdtack x : tau$.
  2. By inversion, we have $x : sigma in Gamma$ (a) and $Gamma tack sigma <= tau$ (b).
  3. We have $Gamma tack x : tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack x : tau$,
        rule(
          $Gamma tack x : sigma$,
          rule(
            $x : sigma in Gamma$,
            $(2. a)$
          )
        ),
        rule(
          $Gamma tack sigma <= tau$,
          $(2.b)$
        )
      )
    )
  $

  - *Case* $elet x = e_1 ein e_2$.
  1. Let us assume $Gamma sdtack elet x = e_1 ein e_2 : tau$.
  2. By inversion, we have $Gamma, cal(V) sdtack e_1 : tau'$ (a), $cal(V) disjoint Gamma$ (b), and $Gamma, x : tforall(cal(V)) tau' sdtack e_2 : tau$ (c).
  3. By induction (2.a), we have $Gamma, cal(V) tack e_1 : tau'$ (a). By @soundgen (3.a, 2.b), we have \ $Gamma tack e_1 : tforall(cal(V)) tau'$ (b).
  4. By induction (2.c), we have $Gamma, x : tforall(cal(V)) tau' tack e_2 : tau$ (a).
  5. We have $Gamma tack elet x = e_1 ein e_2 : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : tau$,
      rule(
        $Gamma tack e_1 : tforall(cal(V)) tau'$,
        $(3.a)$
      ),
      rule(
        $Gamma, x : tforall(cal(V)) tau' tack e_2 : tau$,
        $(4.a)$
      )
    )
  )
  $


  - *Cases* $efun x -> e$, $e_1 space e_2$, $(e: tau')$, and $ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2$.
  _Trivial, this is identical to their declarative counterpart._

  - *Cases* $efun (etype alpha) -> e$, $erefl$, and $()$.
  _Trivial, equivalent to the declarative counterpart with instantiation._
]

#theorem[_Completeness of the syntax-directed #aml typing judgements_][
  When $Gamma tack e : sigma$, then for some $cal(V) disjoint Gamma$, we also have $Gamma, cal(V) sdtack e : tau$ where $Gamma tack tforall(cal(V)) tau <= sigma$.
]

#proof[
  We proceed by rule induction on $Gamma tack e : sigma$.

  - *Case* (Var)
  1. Let us assume $Gamma tack x : sigma$.
  2. By inversion of the (Var) rule, we have $x : sigma in Gamma$.
  3. Wlog, we write $sigma = tforall(cal(V)) tau$ s.t $cal(V) disjoint Gamma$. We have $Gamma, cal(V) tack sigma <= tau$ with a trivial substituion.
  4. By weakining, we have $x : sigma in Gamma, cal(V)$.
  5. We have $Gamma, cal(V) sdtack x : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma, cal(V) sdtack x : tau$,
      rule(
        $x : sigma in Gamma, cal(V)$,
        $(4)$
      ),

      rule(
        $Gamma, cal(V) tack sigma <= tau$,
        $(3)$
      )
    )
  )
  $
  6. We have $Gamma tack tforall(cal(V)) tau <= sigma$ by reflexivity of $<=$.

  - *Case* (Inst)
  1. Let us assume $Gamma tack e : sigma$.
  2. By inversion of the (Inst) rule, we have $Gamma tack e : sigma'$ (a) and $Gamma tack sigma' <= sigma$ (b).
  3. By induction (2.a), we have $Gamma, cal(V) sdtack e : tau$ (a) and $Gamma tack tforall(cal(V)) tau <= sigma'$ (b).
  4. By transitivity of $<=$ (3.b, 2.b), we have $Gamma tack tforall(cal(V)) tau <= sigma$.

  - *Case* (Gen)
  1. Let us assume $Gamma tack e : sigma$.
  2. By inversion of the (Gen) rule, we have $Gamma, alpha^fflex :: kappa tack e : sigma'$ (a), $alpha disjoint Gamma$ (b), and \ $sigma = tforall(alpha :: kappa) sigma'$ (c).
  3. By induction (2.a), we have $Gamma, alpha^fflex :: kappa, cal(V) sdtack e : tau$ (a), $cal(V) disjoint Gamma$ (b), and \ $Gamma, alpha^fflex :: kappa tack tforall(cal(V)) tau <= sigma'$ (c).
  4. Let $cal(V') = alpha^fflex :: kappa, cal(V)$. By (2.b, 3.b), $cal(V') disjoint Gamma$. By (3.a), $Gamma, cal(V') sdtack e : tau$.
  5. By definition of $<=$ and (3.c), we have $Gamma tack tforall(cal(V')) tau <= tforall(alpha) sigma'$.

  - *Case* (Let)
  1. Let us assume $Gamma tack elet x = e_1 ein e_2 : sigma$
  2. By inversion of the (Let) rule, we have $Gamma tack e_1 : sigma'$ (a), and $Gamma, x : sigma' tack e_2 : sigma$ (b).
  3. By induction (2.a), we have $Gamma, cal(V_1) sdtack e_1 : tau'$ (a), $cal(V_1) disjoint Gamma$ (b), and $Gamma tack tforall(cal(V_1)) tau' <= sigma'$ (c).
  4. By induction (2.b), we have $Gamma, x : sigma', cal(V_2) sdtack e_2 : tau$ (a), $cal(V_2) disjoint Gamma, x : sigma'$ (b), and \ $Gamma tack tforall(cal(V_2)) tau <= sigma$ (c).
  5. By @monotonicity (3.c, 4.a), we have $Gamma, x : tforall(cal(V_1)) tau', cal(V_2) sdtack e_2 : tau$.
  6. By exchange (5, 4.b), we have $Gamma, cal(V_2), x : tforall(cal(V_1)) tau' sdtack e_2 : tau$.
  7. By weakening and exchange (3.a, 3.b, 4.b), we have $Gamma, cal(V_2), cal(V_1) sdtack e_1 : tau'$ (a) and $cal(V_1) disjoint Gamma, cal(V_2)$ (b).
  8. We have $Gamma, cal(V_2) sdtack elet x = e_1 ein e_2 : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma, cal(V_2) sdtack elet x = e_1 ein e_2 : tau$,
      rule(
        $Gamma, cal(V_2), cal(V_1) sdtack e_1 : tau'$,
        $(7.a)$
      ),
      rule(
        $cal(V_1) disjoint Gamma, cal(V_2)$,
        $(7.b)$
      ),
      rule(
        $Gamma, cal(V_2), x : tforall(cal(V_1)) tau' sdtack e_2 : tau$,
        $(6)$
      )
    )
  )
  $

  - *Cases* (Fun), (App), (Annot), and (Match).
  _Trivial, this is identical to their declarative counterpart._


  - *Cases* (TFun).
  1. Let us assume $Gamma tack efun (etype alpha) -> e : sigma$.
  2. By inversion of the (TFun) rule, we have $Gamma, alpha^frigid :: ty tack e : sigma'$ (a), $alpha disjoint Gamma$ (b), \ $alpha in.not dangerous(sigma')$ (c), and $sigma = tforall(alpha) sigma'$ (d).
  3. By induction (2.a), we have $Gamma, alpha^frigid :: ty, cal(V) sdtack e : tau'$ (a), $cal(V) disjoint Gamma, alpha^frigid :: kappa$ (b), and \ $Gamma, alpha :: frigid tack tforall(cal(V)) tau' <= sigma'$ (d).
  4. Wlog $beta disjoint Gamma, cal(V), alpha$. Define $cal(V') = cal(V), beta^fflex :: ty$.
  5. By weakening and exchange (3.a), we have $Gamma, cal(V)', alpha^frigid :: ty sdtack e : tau'$.
  6. By (3.b, 4), we have $alpha disjoint Gamma, cal(V)'$.
  7. By @dangerous-anti-monotonicity-lemma (2.c, 3.d), $alpha in.not dangerous(tforall(cal(V)) tau')$. Since $alpha disjoint cal(V)$, it follows that $alpha in.not dangerous(tau')$.
  8. Define $tau = tau'[alpha := beta]$.
  9. We have $Gamma, cal(V)' tack tforall(alpha) tau' <= tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V') tack tforall(alpha) tau' <= underbrace(tau'[alpha := beta], tau "by (8)")$,
        rule(
          $Gamma, cal(V') tack beta :: ty$,
          rule(
            $beta^fflex :: ty  in Gamma, cal(V')$,
            $(4)$
          )
        ),
        rule(
          $Gamma, cal(V') tack tau'[alpha := beta] <= tau'[alpha := beta]$,
          $"refleixivity of" <=$
        )
      )
    )
  $
  10. We have $Gamma, cal(V)' sdtack efun (etype alpha) -> e : tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V') sdtack efun (etype alpha) -> e : tau$,
        rule(
          $Gamma, cal(V'), alpha^frigid :: ty sdtack e : tau'$,
          $(5)$
        ),
        rule(
          $alpha disjoint Gamma, cal(V')$,
          $(6)$
        ),
        rule(
          $alpha in.not dangerous(tau')$,
          $(7)$
        ),
        rule(
          $Gamma, cal(V') tack tforall(alpha) tau' <= tau$,
          $(9)$
        )
      )
    )
  $
  11. By definition of substitution (4), $(tforall(cal(V)) tau'[alpha := beta])[beta := alpha] = tforall(cal(V)) tau'$
  11. We have $Gamma tack tforall(cal(V')) tau <= sigma$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack tforall((beta, cal(V))) tau'[alpha := beta] <= tforall(alpha) sigma'$,
        rule(
          $Gamma, alpha :: frigid tack tforall((beta, cal(V))) tau'[alpha := beta] <= sigma'$,
          rule(
            $Gamma, alpha^frigid :: ty tack alpha :: ty$,
            rule(
              $alpha^frigid :: ty in Gamma, alpha^frigid :: ty$
            )
          ),
          rule(
            $Gamma, alpha^frigid :: ty tack (tforall(cal(V)) tau'[alpha := beta])[beta := alpha] <= sigma'$,
            rule(
              $Gamma, alpha^frigid :: ty tack tforall(cal(V)) tau' <= sigma'$,
              $(3)$
            ),
            name: [$"by" (11)$]
          )
        ),
        rule(
          $alpha disjoint Gamma$,
          $(2.b)$
        )
      )
    )
  $

  - *Case* (Unit).
  1. Let us assume $Gamma tack () : sigma$.
  2. By inversion of the (Unit) rule, we have $sigma = tforall(scopev :: scope) [scopev]tunit$.
  3. Wlog $scopev' disjoint Gamma$. Define $cal(V) = scopev'^fflex :: scope$.
  4. By (3), we have $cal(V) disjoint Gamma$
  5. We have $Gamma, cal(V) tack scopev' ok$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) tack scopev' :: scope$,
        rule(
          $scopev'^fflex :: scope in Gamma, cal(V)$,
          $(3)$
        )
      )
    )
  $

  6. We have $Gamma, cal(V) tack tforall(scopev) [scopev]tunit <= [scopev']tunit$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) tack tforall(scopev :: scope) [scopev]tunit <= [scopev']tunit$,
        rule(
          $Gamma, cal(V) tack scopev' :: scope$,
          $(5)$
        ),
        rule(
          $Gamma, cal(V) tack [scopev']tunit <= [scopev']tunit$,
          $"refleixitivity of" <=$
        )
      )
    )
  $


  7. We have $Gamma, cal(V) sdtack erefl : [scopev']tunit$ by
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) sdtack erefl : [scopev']tunit$,
        rule(
          $Gamma, cal(V) tack tforall(scopev :: scope) [scopev]tunit <= [scopev']tunit$,
          $(6)$
        )
      )
    )
  $

  8. We now show that $Gamma tack tforall(scopev' :: scope) [scopev']tunit <= tforall(scopev :: scopev) [scopev]tunit$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack tforall(scopev' :: scope) [scopev']tunit <= tforall(scopev :: scope) [scopev]tunit$,
        rule(
          $Gamma, scopev^fflex :: scope tack tforall(scopev') [scopev']tunit <= [scopev]tunit$,
          $"(6)" (alpha "equiv")$
        ),
        rule(
          $scopev disjoint Gamma$,
          $"wlog"$
        )
      )
    )
  $


  - *Case* (Refl).
  _Symmetrical to (Unit)._


]

Having established that any typing derivable in the syntax-directed #aml type system is derivable in the declarative #aml type system (and vice versa), we henceforth use the
syntax-directed type system (implicitly).

_Monotonicity._ We now show that #aml enjoys _monotonicity_: strengthening the type of a free expression variable by making it more general preserves well-typedness. We draw attention to this property since Remy and Garrigue's calculus also has this property. 

#definition[
We can extend the instantiation relation $Gamma tack sigma <= sigma'$ to contexts $Gamma <= Gamma'$ as follows
$
  #proof-tree(
    rule(
      $dot <= dot$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, x : sigma <= Gamma', x : sigma'$,
      $Gamma <= Gamma'$,
      $Gamma' tack sigma <= sigma'$,
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, \_ <= Gamma', \_$,
      $Gamma <= Gamma'$
    )
  )
$
]


#lemma[If $Gamma' <= Gamma$ then:
  - If $Gamma tack tau rigid$, then $Gamma' tack tau rigid$.
  - If $Gamma tack tau ok$, then $Gamma' tack tau ok$.
  - If $Gamma tack Psi ok$, then $Gamma' tack Psi ok$.
  - If $Gamma tack sigma <= sigma'$, then $Gamma' tack sigma <= sigma'$.
] <monotonicity-lemma>

#theorem[_Monotonicity of #aml typing judgements_][
  If $Gamma tack e : tau$ holds and $Gamma' <= Gamma$, then $Gamma' tack e : tau$ holds.
] <monotonicity>
#proof[
  We proceed by structural induction on $e$.
  - *Case* $x$.
  1. Let us assume $Gamma tack x : tau$ (a) and $Gamma' <= Gamma$ (b).
  2. By inversion, we have $x : sigma in Gamma$ (a) and $Gamma tack sigma <= tau$ (b).
  3. By definition of $<=$ (1.b), $x : sigma' in Gamma'$ (a) and $Gamma tack sigma' <= sigma$ (b).
  4. By transitivity of $<=$ (3.b, 2.b), $Gamma tack sigma' <= sigma$.
  5. By @monotonicity-lemma (1.b, 2.a, 3.a), we have $Gamma' tack sigma' <= sigma$ (a) and $Gamma' tack sigma <= tau$ (b).
  6. By transitivity of $<=$ (5.a, 5.b), we have $Gamma' tack sigma' <= tau$.
  7. We have $Gamma' tack x : tau$ by:
  $
    #proof-tree(
    rule(
      $Gamma' tack x : tau$,
      rule(
        $x : sigma' in Gamma'$,
        $(3.a)$
      ),
      rule(
        $Gamma' tack sigma' <= tau$,
        $(6)$
      )
    )
  )
  $

  - *Cases* $erefl$ and $()$.
  _Trivial base cases._

  - *Cases* $efun x -> e$, $e_1 space e_2$, $elet x = e_1 ein e_2$, $efun (etype alpha) -> e$, $(e : tau')$, and \ $ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2$.
  _Trivial inductive cases._
]