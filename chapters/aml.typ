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
#syntax(
  horizontal-spacing: 1.25cm,
  syntax-rule(name: [Type Variables], $alpha, beta, gamma in varset(Ty)$),
  syntax-rule(name: [Scope Variables], $scopev, rho.alt in varset(Scope)$),
  syntax-rule(name: [Equation Names], $eqname in EqName$),
  syntax-rule(name: [Type Constructors], $tformer in TyCon ::= dot arrow dot | dot = dot | tunit$),
  syntax-rule(name: [Types], $tau in Ty ::= alpha | overline(tau) tformer | [Psi] tau$),
  syntax-rule(name: [Type Schemes], $sigma in Scm ::= tau | tforall(scopev) sigma | tforall(alpha) sigma$),
  syntax-rule(name: [Scopes], $Psi in Scope ::= dot | scopev | Psi, phi.alt$),
  syntax-rule(
    name: [Contexts],
    $Gamma in Ctx ::= &dot | Gamma, alpha :: f | Gamma, scopev | Gamma, eqname : tau = tau | Gamma, x: sigma$,
  ),
  syntax-rule(name: [Flexibility], $f ::= fflex | frigid$),
)

// Types
Types consist of type variables ($alpha$) and type constructors ($tformer$). Type constructors include functions ($arrow$), base types (such as $tunit$), and the equality withness type ($=$).

// Ambivalent types
Intuiviely, a _scoped ambivalent type_ is a set of provably equivalent types. Under our equivalece relation, introduced later, $[Psi]tau$ is equivalent to a set of types $[Psi]tau'$
where $tau$ and $tau'$ are provably equal using the equations in $Psi$. An ambivalent type is only _coherent_ (in the context $Gamma$) if the equations in $Psi$ are in $Gamma$. Otherwise, the scope is said to have escaped the context.

// Schemes
Polymorphic types are defined by _type schemes_ in a mostly typical #ml fashion, generalzing over zero or more variables. However, we extend the notion of polymorphism to also quantify over _scope variables_ as well, introducing a form of _scope polymorphism_.

// Contexts
Contexts bind term variables to type schemes, introduce (polymorphic) type and scope variables, and store (named) type equations $eqname: tau = tau'$. Each type variable is associated with a _flexibility_ $f$ which can either be _rigid_ ($frigid$) or _flexible_ ($fflex$), indicating whether the type was introduced by an explicit $efun (etype alpha) -> e$ quantifier or implicitly due to let-polymorphism.
Contexts are ordered and duplicates are disallowed. We write $Gamma, Gamma'$ for the concatenation of two contexts (assuming disjointness holds). We write $dom(Gamma)$ for the _domain_ of the context, which informally represents the set of type and scope variables, term variables and equation names. We often write $overline(e) disjoint Gamma$ as a shorthand for $overline(e) disjoint dom(Gamma)$.

We assume types, type schemes, and scopes are equivalent modulo $alpha$-renaming.

The definition for the set of free variables on types, scopes, and schemes is mostly standard.

$
  fv_Ty (alpha) &= { alpha } &&& fv_Scope (dot) &= emptyset \
  fv_Ty (overline(tau) tformer) &= union.big_i fv_Ty (tau_i) &&& fv_Scope (scopev) &= { scopev } \
  fv_Ty ([Psi] tau) &= fv_Scope (Psi) union fv_Ty (tau) &#h(2cm)&& fv_Scope (Psi, eqname) &= fv_Scope (Psi)  \ \
$
$
  fv_Scm (tau) &= fv_Ty (tau) \
  fv_Scm (tforall(alpha) sigma) &= fv_Scm (sigma) \\ { alpha } \
  fv_Scm (tforall(scopev) sigma) &= fv_Scm (sigma) \\ { scopev }
$



_Well-formedness_. Well-formedness judgements for types, type schemes, and contexts ensure the soundness of scoped ambivalent types and the coherent use of variables.


#judgement-box($Gamma tack Psi ok$, $Gamma tack tau rigid$, $Gamma tack tau ok$, $Gamma tack sigma ok$, $Gamma ok$)

$
  #proof-tree(
    rule(
      $Gamma tack dot ok$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack scopev ok$,
      $scopev in dom(Gamma)$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack Psi, eqname ok$,
      $Gamma tack Psi ok$,
      $eqname in dom(Gamma)$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack alpha ok$,
      $alpha in dom(Gamma)$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(tau) tformer ok$,
      $forall i. space Gamma tack tau_i ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack [Psi] tau ok$,
      $Gamma tack Psi ok$,
      $Gamma tack tau rigid$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack alpha rigid$,
      $alpha : frigid in Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(tau) tformer rigid$,
      $forall i. space Gamma tack tau_i rigid$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack tforall(alpha) sigma ok$,
      $Gamma, alpha tack sigma ok$,
      $alpha disjoint Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tforall(scopev) sigma ok$,
      $Gamma, scopev tack sigma ok$,
      $scopev disjoint Gamma$
    )
  )

  #v2

  #proof-tree(
   rule(
      $dot ok$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, alpha ok$,
      $Gamma ok$,
      $alpha disjoint Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, scopev ok$,
      $Gamma ok$,
      $scopev disjoint Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma, eqname: tau_1 = tau_2 ok$,
      $Gamma ok$,
      $Gamma tack tau_1 rigid$,
      $Gamma tack tau_2 rigid$,
      $eqname disjoint Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, x : sigma ok$,
      $Gamma ok$,
      $Gamma tack sigma ok$,
      $x disjoint Gamma$
    )
  )
$

It is interesting to note that types $tau$ _under_ a scope $Psi$ must be _rigid_. This restriction, inherited from Remy and Garrigue's [??] work on ambivalent types, simplifies our presentation and is sufficient to encode OCaml's behaviour.

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
      $Gamma tack tau ok$
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
We assume well-formedness for contexts $Gamma ok$. The typing rules are given below.




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
      $Gamma tack tau_1 ok$
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
      $Gamma tack e : tforall(alpha) sigma$,
      $Gamma, alpha :: fflex tack e : sigma$,
      $alpha disjoint Gamma$,
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun (etype alpha) -> e : tforall(alpha) sigma$,
      $Gamma, alpha :: frigid tack e : sigma$,
      $alpha disjoint Gamma$,
      $alpha in.not dangerous(sigma)$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau_2$,
      $Gamma tack e : tau_1$,
      $Gamma tack tau_1 >= forall ceil(tau rigid) <= tau_2$,
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack e : tforall(scopev) sigma$,
      $Gamma, scopev tack e : sigma$,
      $scopev disjoint Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : tforall(alpha) alpha = alpha$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack () : tforall(scopev) [scopev]tunit$,
      $$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : sigma$,
      $Gamma tack e_1 : tau$,
      $Gamma tack forall ceil(tau_1 = tau_2 rigid) <= tau$,
      $eqname disjoint Gamma$,
      $Gamma, eqname : tau_1 = tau_2 tack e_2 : sigma$,
      $Gamma tack sigma ok$,
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
    $Gamma tack tforall(alpha) sigma <= sigma'$,
    $Gamma tack tau ok$,
    $Gamma tack sigma[alpha := tau] <= sigma'$
  )
)

#h1

#proof-tree(
  rule(
    $Gamma tack tforall(scopev) sigma <= sigma'$,
    $Gamma tack Psi ok$,
    $Gamma tack sigma[scopev := Psi] <= sigma'$
  )
)

#v2

#proof-tree(
  rule(
    $Gamma tack sigma <= tforall(alpha) sigma'$,
    $Gamma, alpha :: f tack sigma <= sigma'$,
    $alpha disjoint Gamma$
  )
)

#h1

#proof-tree(
  rule(
    $Gamma tack sigma <= forall scopev. sigma'$,
    $Gamma, scopev tack sigma <= sigma'$,
    $scopev disjoint Gamma$
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
Pattern matching on equalities using $ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2$ can eliminate the equality witness $e_1$ of type $tau_1 = tau_2$, adding it as an implicit equality to the context $Gamma$ while type checking the body $e_2$; the witness $e_1$ must have the structure of $tau_1 = tau_2$ but may have additional scopes -- we formalize this using a _scope erasure_ function. Since the equation is only available in the scope of $e_2$, it must not be present in the return type $sigma$. We ensure this by allocating a fresh name for the equality $eqname disjoint Gamma$ and ensuring $eqname$ doesn't occur in $sigma$, this is done so by using the well-formedness judgement $Gamma tack sigma ok$.
If the return type doesn't satisfy this condition, then we say the _equation ($eqname$) has escaped its scope_.

_Annotations_. Annotations represent an explicit loss of sharing of scopes between types. This loss of sharing of scopes permits us to eliminate ambivalence in our return type, thereby preventing scope escapes. The types $tau_1, tau_2$ need not be identical to $tau$ but must instead be _consistent instances_ of $tau$. We define what is means to be a _consistent instance_ below.

// Rigid instances definition
We begin by defining a _scope insertion_ function $ceil(tau rigid)$ for rigid types, which produces a context of scope variables $cal(S)$ and a type $tau'$ with scopes inserted at _leaves_ of the type. Scopes at inner nodes can be inferred via the distributivity of scopes.

#let ceilret(a, b) = $#a triangle.r.small #b$
$
  ceil(alpha rigid) &= ceilret(scopev, [scopev]alpha) &&"fresh" scopev \
  ceil(tformer rigid) &= ceilret(scopev, [scopev]tformer) &&"fresh" scopev \
  ceil(overline(tau) tformer rigid) &= ceilret(#[$cal(S)_1, ..., cal(S)_n$], overline(tau')) tformer &#h(2cm)&"where" ceil(tau_i rigid) = ceilret(cal(S)_i, tau'_i)
$

We write $forall ceil(tau rigid)$ for $tforall(cal(S)) tau'$ where $ceil(tau rigid) = ceilret(cal(S), tau')$. This type scheme describes a set of instances that are equivalent to $tau$ after _scope erasure_. We say such instances are _consistent instances_ of $tau$. Formally, they satisfy the following:
$
  forall tau'. space Gamma tack forall ceil(tau rigid) <= tau' ==> exists tau''. space Gamma tack tau' equiv tau'' and floor(tau'') = tau
$
where _scope erasure_, denoted $floor(tau)$, is defined as:
$
  floor(alpha) &= alpha \
  floor(overline(tau) tformer) &= overline(floor(tau)) tformer \
  floor([Psi]tau) &= floor(tau)
$

We use the following judgement to check whether $sigma$ is a consistent instance of $tau$:
$
  #proof-tree(
    rule(
      $Gamma tack forall ceil(tau rigid) <= sigma$,
      $Gamma tack tau rigid$,
      $Gamma tack forall ceil(tau rigid) <= sigma$
    )
  )
$
We note that $Gamma tack forall ceil(tau rigid) ok$ is implied by $Gamma tack tau rigid$, as stated in ??.
To check that both $tau_1$ and $tau_2$ are consistent instances of $tau$, we use the following shorthand $Gamma tack tau_1 >= forall ceil(tau rigid) <= tau_2$ for $Gamma tack forall ceil(tau rigid) <= tau_1$ _and_ $Gamma tack forall ceil(tau rigid) <= tau_2$.


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
  // Should dangerous should only be a subset of the free variables of the input?
  dangerous(tforall(alpha) sigma) &= dangerous(sigma) \\ {alpha} \
  // No need to use set-minus here since dangerous is a set of _type_ variables
  dangerous(tforall(scopev) sigma) &= dangerous(sigma)
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

We now formalize two important properties of our calculus, _monotonicity_ and _stability_. Both are cruicial for proving that constraint generation is sound and complete with respect to #aml's typing judgements. 

#definition[A context $Theta$ is _soft_ if it only consists of $alpha :: f$ and $scopev$.]

#theorem("Weakening")[
  Suppose $Gamma, Theta, Delta ok$. Then
  + If $Gamma, Delta tack tau rigid$, then $Gamma, Theta, Delta tack tau rigid$
  + If $Gamma, Delta tack tau ok$, then $Gamma, Theta, Delta tack tau ok$
  + If $Gamma, Delta tack Psi ok$, then $Gamma, Theta, Delta tack Psi ok$
  + If $Gamma, Delta tack tau equiv tau'$, then $Gamma, Theta, Delta tack tau equiv tau'$
  + If $Gamma, Delta tack e : sigma$, then $Gamma, Theta, Delta tack e : sigma$
]
#proof[
  By induction on the derivation. 
]

#theorem("Type Exchange")[
  Suppose $Theta, Delta$ are soft. Then
  + If $Gamma, Theta, Delta tack tau rigid$, then $Gamma, Delta, Theta tack tau rigid$. 
  + If $Gamma, Theta, Delta tack tau ok$, then $Gamma, Delta, Theta tack tau ok$. 
  + If $Gamma, Theta, Delta tack Psi ok$, then $Gamma, Delta, Theta tack Psi ok$. 
  + If $Gamma, Theta, Delta tack tau equiv tau'$, then $Gamma, Delta, Theta tack tau equiv tau'$
  + If $Gamma, Theta, Delta tack e : sigma$, then $Gamma, Delta, Theta tack e : sigma$
]
#proof[
  By induction on the derivation. 
]

#theorem("Type and Scope Substitution")[
  Suppose $Gamma tack tau ok$ and $Gamma tack Psi ok$. Then 
  + If $Gamma, alpha :: fflex, Delta tack tau' ok$, then $Gamma, Delta[alpha := tau] tack tau'[alpha := tau] ok$
  + If $Gamma, scopev, Delta tack Psi' ok$, then $Gamma, Delta[scopev := Psi] tack Psi'[scopev := Psi] ok$
  + If $Gamma, scopev, Delta tack tau' ok$, then $Gamma, Delta[scopev := Psi] tack tau'[scopev := Psi] ok$
  + If $Gamma, alpha :: fflex, Delta tack sigma <= sigma'$, then $Gamma, Delta[alpha := tau] tack sigma[alpha := tau] <= sigma'[alpha := tau]$
  + If $Gamma, scopev, Delta tack sigma <= sigma'$, then $Gamma, Delta[scopev := Psi] tack sigma[scopev := Psi] <= sigma'[scopev := Psi]$
]
#proof[
  By induction on the derivation of the substitutee. 
]


#theorem("Well-formedness Properties")[
  Suppose $Gamma ok$. 
  + If $Gamma tack tau rigid$, then $Gamma tack tau ok$. 
  + If $Gamma; Psi tack tau_1 equiv tau_2$, then $Gamma tack tau_1 rigid$ and $Gamma tack tau_2 rigid$. 
  + If $Gamma tack tau_1 equiv tau_2$, then $Gamma tack tau_1 ok$ and $Gamma tack tau_2 ok$. 
  + If $Gamma tack sigma_1 <= sigma_2$ and $Gamma tack sigma_1 ok$, then $Gamma tack sigma_2 ok$. 
  + If $Gamma tack e : sigma$, then $Gamma tack sigma ok$. 
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
      $Gamma tack tau_1 ok$
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
      $Gamma, alpha :: frigid tack e : tau$,
      $alpha disjoint Gamma$,
      $alpha in.not dangerous(tau)$,
      $Gamma tack tforall(alpha) tau <= tau'$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau_2$,
      $Gamma tack e : tau_1$,
      $Gamma tack tau_1 >= forall ceil(tau rigid) <= tau_2$,
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : tau$,
      $Gamma tack tforall(alpha) alpha = alpha <=  tau$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack () : tau$,
      $Gamma tack tforall(scopev) [scopev]tunit <= tau$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : tau$,
      $Gamma tack e_1 : tau'$,
      $Gamma tack forall ceil(tau_1 = tau_2 rigid) <= tau'$,
      $eqname disjoint Gamma$,
      $Gamma, eqname : tau_1 = tau_2 tack e_2 : tau$,
      $Gamma tack tau ok$,
    )
  )
$


We write $cal(V)$ for a sequence of non-rigid generalizable variables in the context. Rather than inlining subsumption (as is standard), we keep it explicit, 
since each inlining would produce an explicit $equiv$-equivalence, which does not improve readability. 

#lemma[_Soundness of generalization_][
  If $Gamma, cal(V) tack e : tau$ and $cal(V) disjoint Gamma$ then $Gamma tack e : tforall(cal(V)) tau$.
] <soundgen>
#proof[
  Trivial proof by induction on the cardinality of $cal(V)$.
]

#lemma[
  Given $alpha in.not textsf("eqs")(Gamma)$. 

  + If $Gamma tack tau equiv tau'$ and $alpha in.not dangerous(tau')$, then $alpha in.not dangerous(tau)$
  + If $Gamma tack sigma <= sigma'$ $alpha in.not dangerous(sigma')$, then $alpha in.not dangerous(sigma)$] <dangerous-anti-monotonicity-lemma>

#proof[
  + Induction on the derivation $Gamma tack tau equiv tau'$. 
  
  + 
    We proceed by induction on the derivation of $Gamma tack sigma <= sigma'$. 
    - *Case* (Equiv)
    Use (1)

    - *Case* ($forall$L)
    1. Let us assume $Gamma tack sigma <= sigma'$. 
    2. By inversion of the ($forall$L) rule, we have $sigma = tforall(beta) sigma''$ (a), $Gamma tack tau ok$ (b), and\ 
      $Gamma tack sigma''[beta := tau] <= sigma'$ (c). 
    3. By induction (2.c), we have $alpha in.not dangerous(sigma''[beta := tau])$
    4. By (3), we conclude $alpha in.not dangerous(sigma'')$ and $alpha in.not dangerous(tau)$. 
    5. By (4), $alpha in.not dangerous(tforall(beta) sigma'')$

    - *Case* ($forall$R)
    1. Let us assume $Gamma tack sigma <= sigma'$.
    2. By inversion of the ($forall$R) rule, we have $sigma' = tforall(beta) sigma''$ (a), $beta disjoint Gamma$ (b), and $Gamma, beta :: f tack sigma <= sigma''$
    3. By induction (2.c), we have $alpha in.not dangerous(sigma)$
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

  - *Case* (Gen-$alpha$)
  1. Let us assume $Gamma tack e : sigma$.
  2. By inversion of the (Gen-$alpha$) rule, we have $Gamma, alpha :: fflex tack e : sigma'$ (a), $alpha disjoint Gamma$ (b), and \ $sigma = tforall(alpha) sigma'$ (c).
  3. By induction (2.a), we have $Gamma, alpha :: fflex, cal(V) sdtack e : tau$ (a), $cal(V) disjoint Gamma$ (b), and \ $Gamma, alpha :: fflex tack tforall(cal(V)) tau <= sigma'$ (c).
  4. Let $cal(V') = alpha :: fflex, cal(V)$. By (2.b, 3.b), $cal(V') disjoint Gamma$. By (3.a), $Gamma, cal(V') sdtack e : tau$.
  5. By defn. of $<=$ and (3.c), we have $Gamma tack tforall(cal(V')) tau <= tforall(alpha) sigma'$.

  - *Case* (Gen-$scopev$)
  _Symmetrical to (Gen-$alpha$)._

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
  2. By inversion of the (TFun) rule, we have $Gamma, alpha :: frigid tack e : sigma'$ (a), $alpha disjoint Gamma$ (b), \ $alpha in.not dangerous(sigma')$ (c), and $sigma = tforall(alpha) sigma'$ (d).
  3. By induction (2.a), we have $Gamma, alpha :: frigid, cal(V) sdtack e : tau'$ (a), $cal(V) disjoint Gamma, alpha :: frigid$ (b), and \ $Gamma, alpha :: frigid tack tforall(cal(V)) tau' <= sigma'$ (d).
  4. Wlog $beta disjoint Gamma, cal(V), alpha$. Define $cal(V') = cal(V), beta :: fflex$.
  5. By weakening and exchange (3.a), we have $Gamma, cal(V)', alpha :: frigid sdtack e : tau'$.
  6. By (3.b, 4), we have $alpha disjoint Gamma, cal(V)'$.
  7. By @dangerous-anti-monotonicity-lemma (2.c, 3.d), $alpha in.not dangerous(tforall(cal(V)) tau')$. Since $alpha disjoint cal(V)$, it follows that $alpha in.not dangerous(tau')$.
  8. Define $tau = tau'[alpha := beta]$.
  9. We have $Gamma, cal(V)' tack tforall(alpha) tau' <= tau$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V') tack tforall(alpha) tau' <= underbrace(tau'[alpha := beta], tau "by (8)")$,
        rule(
          $Gamma, cal(V') tack beta ok$,
          rule(
            $beta in Gamma, cal(V')$,
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
          $Gamma, cal(V'), alpha :: frigid sdtack e : tau'$,
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
            $Gamma, alpha :: frigid tack alpha ok$,
            rule(
              $alpha in Gamma, alpha :: frigid$
            )
          ),
          rule(
            $Gamma, alpha :: frigid tack (tforall(cal(V)) tau'[alpha := beta])[beta := alpha] <= sigma'$,
            rule(
              $Gamma, alpha :: frigid tack tforall(cal(V)) tau' <= sigma'$,
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
  2. By inversion of the (Unit) rule, we have $sigma = tforall(scopev) [scopev]tunit$.
  3. Wlog $scopev' disjoint Gamma$. Define $cal(V) = scopev'$.
  4. By (3), we have $cal(V) disjoint Gamma$
  5. We have $Gamma, cal(V) tack scopev' ok$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) tack scopev' ok$,
        rule(
          $scopev' in Gamma, cal(V)$,
          $(3)$
        )
      )
    )
  $

  6. We have $Gamma, cal(V) tack tforall(scopev) [scopev]tunit <= [scopev']tunit$ by:
  $
    #proof-tree(
      rule(
        $Gamma, cal(V) tack tforall(scopev) [scopev]tunit <= [scopev']tunit$,
        rule(
          $Gamma, cal(V) tack scopev' ok$,
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
          $Gamma, cal(V) tack tforall(scopev) [scopev]tunit <= [scopev']tunit$,
          $(6)$
        )
      )
    )
  $

  8. We now show that $Gamma tack tforall(scopev') [scopev']tunit <= tforall(scopev) [scopev]tunit$ by:
  $
    #proof-tree(
      rule(
        $Gamma tack tforall(scopev') [scopev']tunit <= tforall(scopev) [scopev]tunit$,
        rule(
          $Gamma, scopev tack tforall(scopev') [scopev']tunit <= [scopev]tunit$,
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

_Contextual Substitutions_. Substitutions are crucial to prove soundness and completeness of constraint generation. However, substitutions in our system pose a difficutly with respect 
to well-formedness (which must be strictly adhered to in #aml). Instead, taking inspiration on Dunfield and Krishnaswami [??], we develop a notion of an _ordered contextual substitution_, which permit us to define the variables' scope and control the free variables and equations of their solutions. 

Like a context $Gamma$, contextual substitutions $Phi$ (Figure ??) contain declarations of variables, equations and type scheme bindings. Unlike contexts, contextual substitutions contain 
mappings from _flexible_ variables to solutions ($scopev := Psi$ and $alpha :: fflex := tau$). The well-formedness rules for contextual substitutions are given in Figure ??. We frequently consider contexts $Gamma$ as contextual substitutions. 

#syntax(
  syntax-rule(name: [Contextual \ Substitutions], 
  $Phi, Xi ::= &dot | Phi, scopev | Phi, alpha :: f | Phi, eqname : tau = tau | Phi, x : sigma \ 
  | &Phi, scopev := Psi | Phi, alpha ::fflex := tau$)
)

#judgement-box($Phi ok$)
$
  #proof-tree(
    rule(
      $dot ok$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Phi, scopev ok $, 
      $Phi ok$, 
      $scopev disjoint Phi$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Phi, alpha :: f ok$, 
      $Phi ok$, 
      $alpha disjoint Phi$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Phi, x : sigma ok$, 
      $Phi ok$, 
      $Phi tack sigma ok$, 
      $x disjoint Phi$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Phi, eqname : tau_1 = tau_2 ok$, 
      $Phi ok$, 
      $Phi tack tau_1 rigid$, 
      $Phi tack tau_2 rigid$, 
      $eqname disjoint Phi$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Phi, scopev := Psi ok $, 
      $Phi ok $, 
      $Phi tack Psi ok$, 
      $scopev disjoint Phi$
    )
  ) 

  #v1 

  #proof-tree(
    rule(
      $Phi, alpha :: fflex := tau ok$, 
      $Phi ok$, 
      $Phi tack tau ok$, 
      $alpha disjoint Phi$
    )
  )
$

The well-formedness rules for contextual substitutions enforce scoping. Consequently, circularity of substitutions is ruled out: $alpha :: fflex = beta, beta :: fflex = alpha$ is not well-formed. 
All rules regarding judgements regarding types and schemes above may be verbatim translated for contextual substitutions. 

Contextual substitutions can be applied to type and scopes. We write $[Phi]tau$ and $[Phi]Psi$ for $Phi$ applies as a substitution to $tau$ and $Psi$ respectively; this operation is defined below: 
$
  [Phi]alpha &= cases(
    alpha &#h1&"if" alpha :: f in Phi, 
    [Phi]tau &&"if" alpha :: fflex := tau in Phi
  ) \
  [Phi](overline(tau) tformer) &= overline([Phi]tau) tformer \ 
  [Phi]([Psi]tau) &= [[Phi]Psi]([Phi]tau) \ \ 

  [Phi]dot &= dot \ 
  [Phi]scopev &= cases(
    scopev &#h1&"if" scopev in Phi, 
    [Phi]Psi &&"if" scopev := Psi in Phi 
  ) \
  [Phi](Psi, eqname) &= [Phi]Psi, eqname 
$
Subsitution can be extended to be applied to type schemes in the typical capture avoiding way. 


_Contextual extension._ We introduce a context extension judgement $Phi --> Xi$. This judgement captures a notion of 
that a given context may be "more solved" by adding solutions to flexible variables. A _complete_ 
contextual substitution $Omega$ is a substitution where _every_ flexible variable has a solution. 
Contextual extension also relates substitution with complete substitutions. 

#judgement-box($Phi --> Xi$)
$
  #proof-tree(
    rule(
      $dot --> dot$, 
      $$
    )
  )  

  #h1

  #comment[TODO] 
$


_Contextual application._ We can apply any contextual substitution $Phi$ to any substitution $Xi$ that it extends. The opertation of application $[Phi]Xi$ is given below. 
For contexts $Gamma$, we require $Gamma --> Phi$. 

$
  [dot]dot &= dot \ 
  [Phi, x : sigma](Xi, x : sigma') &= [Phi]Xi, x : [Phi]sigma &#h1&"if" [Phi]sigma = [Phi]sigma' \ 
  [Phi, eqname : tau_1 = tau_2](Xi, eqname : tau_1 = tau_2) &= [Phi]Xi, eqname : tau_1 = tau_2 \ 
  [Phi, alpha :: f](Xi, alpha :: f) &= [Phi]Xi, alpha :: f \
  [Phi, alpha :: fflex := tau](Xi, alpha :: fflex) &= [Phi]Xi \ 
  [Phi, alpha :: fflex := tau](Xi, alpha :: fflex := tau') &= [Phi]Xi &&"if" [Phi]tau = [Phi]tau' \ 
  [Phi, scopev](Xi, scopev) &= [Phi]Xi, scopev \ 
  [Phi, scopev = Psi](Xi, scopev) &= [Phi]Xi \
  [Phi, scopev = Psi](Xi, scopev = Psi') &= [Phi]Xi &&"if" [Phi]Psi = [Phi]Psi' \
  #comment[Maybe also add?] \
  [Phi, alpha :: fflex := tau]Xi &= [Phi]Xi &&"if" alpha in.not dom(Phi) 
$




#lemma[
  Given $Gamma --> Phi$. 
  + If $Gamma tack tau ok$, then $[Phi]Gamma tack [Phi]tau ok$.
  + If $Gamma tack tau rigid$, then $[Phi]Gamma tack tau rigid$.
  + If $Gamma tack Psi ok$, then $[Phi]Gamma tack [Phi]Psi ok$. 
  + If $Gamma tack sigma <= sigma'$, then $[Phi]Gamma tack [Phi]sigma <= [Phi]sigma'$.
] <subst-stable-lemma>
#proof[
  + We proceed by induction on $Gamma tack tau ok$
    - *Case* (Var)
    + Let us assume $Gamma tack alpha ok$
    + By inversion of (Var), we have $alpha :: f in Gamma$ 
    + Split case on $f$:
      - $f = frigid$. 

        a. By definition of extension (3), $alpha :: frigid in Phi$

        b. By definition of substitution (a), $[Phi]alpha = alpha$

        c. By definition of application (2, a), $alpha :: frigid in [Phi]Gamma$

        d. We have $[Phi]Gamma tack [Phi]alpha ok$ by 
        $
          #proof-tree(
            rule(
              $[Phi]Gamma tack underbrace(alpha, [Phi]alpha "by (b)") ok $, 
              rule(
                $alpha :: frigid in [Phi]Gamma$, 
                $(c)$
              )
            )
          )
        $ 

      - $f = fflex$.

        a. By definition of extension (3), we either have $alpha :: fflex in Phi$ or $alpha :: fflex := tau in Phi$

        b. Split case on (a)

        - $alpha :: fflex in Phi$. 

        _Symmetrical to rigid case._ 

        - $alpha :: fflex := tau in Phi$

          i. By (2), we have $Gamma = Gamma_L, alpha :: fflex, Gamma_R$

          ii. We have $Phi = Phi_L, alpha :: fflex := tau, Phi_R$. 

          iii. By extension, we have $Phi_L tack tau ok$. 

          iv. We have $[Phi]alpha = [Phi]tau$ 

          v. 
          $
            Phi tack [Phi]tau ok
          $
          RTP $[Phi]Gamma tack [Phi]tau ok$
          
          Not the case e.g. 

          $
            
            Phi = beta :: fflex, gamma :: fflex, alpha :: fflex := beta -> gamma \
            Gamma = alpha :: fflex 
          $
]


#lemma[
  + If $alpha in.not dangerous(tau)$ and $Phi[alpha :: frigid]$, then $alpha in.not dangerous([Phi]tau)$.
]

#theorem[_#aml typing judgements are stable under substitutions_][
  Given $Gamma --> Phi$. 
  If $Gamma tack e : tau$, then $[Phi]Gamma tack e : [Phi]tau$
] <subst-stable>
#proof[
  We proceed by structural induction on $e$.
  - *Case* $x$.
  1. Let us assume $Gamma tack x : tau$
  2. By inversion, we have $x: sigma in Gamma$ (a) and $Gamma tack sigma <= tau$ (b).
  3. By (2.a), $x : theta(sigma) in theta(Gamma)$.
  4. By @subst-stable-lemma (2.b), $theta(Gamma) tack theta(sigma) <= theta(tau)$
  5. We have $theta(Gamma) tack x : theta(tau)$ by:
  $
    #proof-tree(
  rule(
    $theta(Gamma) tack x : theta(tau)$,
    rule(
      $x : theta(sigma) in theta(Gamma)$,
      $(3)$
    ),
    rule(
      $theta(Gamma) tack theta(sigma) <= theta(tau)$,
      $(4)$
    )
  )
)
  $

  - *Case* $efun x -> e$.
  1. Let us assume $Gamma tack efun x -> e : tau$.
  2. By inversion, we have $Gamma, x : tau_1 tack e : tau_2$ (a), $Gamma tack tau_1 ok$ (b), and $tau = tau_1 -> tau_2$ (c).
  3. By induction (2.a), we have $theta(Gamma, x : tau_1) tack e : theta(tau_2)$. By definition, \ $theta(Gamma, x : tau_1) = theta(Gamma), x : theta(tau_1)$. So we have $theta(Gamma), x : theta(tau_1) tack e : tau(theta_2)$.
  4. By definition of substitution (2.c), $theta(tau) = theta(tau_1) -> theta(tau_2)$.
  5. By @subst-stable-lemma (2.b), $theta(Gamma) tack theta(tau_1) ok$.
  6. We have $theta(Gamma) tack efun x -> e : theta(tau)$ by:
  $
    #proof-tree(
  rule(
    $theta(Gamma) tack efun x -> e : underbrace(theta(tau_1) -> theta(tau_2), theta(tau) "by (4)")$,
    rule(
      $theta(Gamma), x : theta(tau_1) tack e : theta(tau_2)$,
      $(3)$
    ),
    rule(
      $theta(Gamma) tack theta(tau_1) ok$,
      $(5)$
    )
  )
)
  $

  - *Case* $e_1 space e_2$.
  1. Let us assume $Gamma tack e_1 space e_2 : tau$.
  2. By inversion, we have $Gamma tack e_1 : tau' -> tau$ (a) and $Gamma tack e_2 : tau'$ (b).
  3. By induction (2.a), we have $theta(Gamma) tack e_1 : theta(tau' -> tau)$. By definition, \ $theta(tau' -> tau) = theta(tau') -> theta(tau)$. So we have $theta(Gamma) tack e_1 : theta(tau') -> theta(tau)$.
  4. By induction (2.b), we have $theta(Gamma) tack e_2 : theta(tau')$
  5. We have $theta(Gamma) tack e_1 space e_2 : theta(tau)$ by:
  $
    #proof-tree(
    rule(
      $theta(Gamma) tack e_1 space e_2 : theta(tau)$,
      rule(
        $theta(Gamma) tack e_1 : theta(tau') -> theta(tau)$,
        $(3)$
      ),
      rule(
        $theta(Gamma) tack e_2 : theta(tau')$,
        $(4)$
      )
    )
  )
  $


  - *Case* $elet x = e_1 ein e_2$.
  1. Let us assume $Gamma tack elet x = e_1 ein e_2 : tau$.
  2. By inversion, we have $Gamma, cal(V) tack e_1 : tau'$ (a), $cal(V) disjoint Gamma$ (b), and $Gamma, x : tforall(cal(V)) tau' tack e_2 : tau$ (c).
  3. Wlog $cal(V) disjoint theta$.
  4. By induction (2.a), we have $theta(Gamma, cal(V)) tack e_1 : theta(tau')$. By (3) and definition of substitution on contexts, $theta(Gamma, cal(V)) = theta(Gamma), cal(V)$. So we have $theta(Gamma), cal(V) tack e_1 : theta(tau')$.
  5. By induction (2.c), we have $theta(Gamma, x : tforall(cal(V)) tau') tack e_2 : theta(tau)$. By definition of substition and (3), $theta(Gamma, x : tforall(cal(V)) tau') = theta(Gamma), x : tforall(cal(V)) theta(tau')$. So we have $theta(Gamma), x : tforall(cal(V)) theta(tau') tack e_2 : theta(tau)$.
  6. By (3) and (2.b), $cal(V) disjoint theta(Gamma)$.
  7. We have $theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau)$ by:
  $
    #proof-tree(
    rule(
      $theta(Gamma) tack elet x = e_1 ein e_2 : theta(tau)$,
      rule(
        $theta(Gamma), cal(V) tack e_1 : theta(tau')$,
        $(4)$
      ),
      rule(
        $cal(V) disjoint theta(Gamma)$,
        $(6)$
      ),
      rule(
        $theta(Gamma), x : tforall(cal(V)) theta(tau) tack e_2 : theta(tau)$,
        $(5)$
      )
    )
  )
  $

  - *Case* $efun (etype alpha) -> e$.

  1. Let us assume $Gamma tack efun (etype alpha) -> e : tau$
  2. By inversion, we have $Gamma, alpha :: frigid tack e : tau'$ (a), $alpha \# Gamma$ (b), $alpha in.not dangerous(tau')$ (c), and \ $Gamma tack tforall(alpha) tau' <= tau$ (d).
  3. Wlog $alpha disjoint theta$.
  4. By induction (2.a), $theta(Gamma, alpha :: frigid) tack e : theta(tau')$. By definition of substitution and (3), we have $theta(Gamma, alpha :: frigid) = theta(Gamma), alpha :: frigid$. So we have $theta(Gamma), alpha :: frigid tack e : theta(tau')$.
  5. By (2.b) and (3), we have $alpha disjoint theta(Gamma)$.
  6. By @subst-stable-lemma (2.c, 3), $alpha in.not dangerous(theta(tau'))$.
  7. By @subst-stable-lemma (2.d) and (3.a), we have $theta(Gamma) tack tforall(alpha) theta(tau') <= theta(tau)$.
  8. We have $theta(Gamma) tack efun (etype alpha) -> e : theta(tau)$ by:
  $
    #proof-tree(
  rule(
    $theta(Gamma) tack efun (etype alpha) -> e : theta(tau)$,
    rule(
      $theta(Gamma), alpha :: frigid tack e : theta(tau')$,
      $(4)$
    ),
    rule(
      $alpha disjoint theta(Gamma)$,
      $(5)$
    ),
    rule(
      $alpha in.not dangerous(theta(tau'))$,
      $(6)$
    ),
    rule(
      $theta(Gamma) tack tforall(alpha) theta(tau') <= theta(tau) ok$,
      $(7)$
    )

  )
)
  $



  - *Case* $(e : tau')$.
  1. Let us assume $Gamma tack (e : tau') : tau$
  2. By inversion, we have $Gamma tack e : tau''$ (a) and $Gamma tack tau'' >= forall ceil(tau' rigid) <= tau$ (b)
  3. By induction (2.a), we have $theta(Gamma) tack e : theta(tau'')$.
  4. $fv(tau') disjoint theta$
  5. By @subst-stable-lemma (2.b), $theta(Gamma) tack theta(tau'') >= theta(forall ceil(tau' rigid)) <= theta(tau)$. By (4), we have $theta(forall ceil(tau' rigid)) = forall ceil(tau' rigid)$.
  6. We have $theta(Gamma) tack (e : tau') : theta(tau)$ by:
  $
    #proof-tree(
    rule(
      $theta(Gamma) tack (e : tau') : theta(tau)$,

      rule(
        $theta(Gamma) tack e : theta(tau'')$,
        $(3)$
      ),
      rule(
        $theta(Gamma) tack theta(tau'') >= forall ceil(tau' rigid) <= theta(tau)$,
        $(5)$
      )
    )
  )
  $

  - *Case* $erefl$.
  1. Let us assume $Gamma tack erefl : tau$.
  2. By inversion, we have $Gamma tack tforall(alpha) alpha = alpha <= tau$.
  3. By @subst-stable-lemma (2), $theta(Gamma) tack theta(tforall(alpha) alpha = alpha) <= theta(tau)$.
  4. Wlog $alpha disjoint theta$.
  5. By definition of substitution (4), $theta(tforall(alpha) alpha = alpha) = tforall(alpha) alpha = alpha$.
  6. By (2, 5), we have $theta(Gamma) tack tforall(alpha) alpha = alpha <= theta(tau)$.
  7. We have $theta(Gamma) tack erefl : theta(tau)$ by:
  $
    #proof-tree(
      rule(
        $theta(Gamma) tack erefl : theta(tau)$,
        rule(
          $theta(Gamma) tack tforall(alpha) alpha = alpha <= theta(tau') ok$,
          $(6)$
        )
      )
    )
  $

  - *Case* $()$.
  1. Let us assume $Gamma tack () : tau$.
  2. By inversion, we have $Gamma tack tforall(scopev) [scopev]tunit <= tau$.
  3. By @subst-stable-lemma (2.a), we have $theta(Gamma) tack theta(tforall(scopev) [scopev]tunit) <= theta(tau)$.
  4. Wlog $scopev disjoint theta$
  5. By definition of substitution (4), $theta(tforall(scopev) [scopev]tunit) = tforall(scopev) [scopev]tunit$.
  6. By (3, 6), we have $theta(Gamma) tack tforall(scopev) [scopev]tunit <= theta(tau)$
  7. We have $theta(Gamma) tack () : theta(tau)$ by:
  $
    #proof-tree(
      rule(
        $theta(Gamma) tack () : theta(tau)$,
        rule(
          $theta(Gamma) tack tforall(scopev) [scopev]tunit <= theta(tau)$,
          $(6)$
        )
      )
    )
  $

  - *Case* $ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2$.
  1. Let us assume $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : tau$.
  2. By inversion, we have $Gamma tack e_1 : tau'$ (a), $Gamma tack forall ceil(tau_1 = tau_2 rigid) <= tau'$ (b), $eqname disjoint Gamma$ (c), \ $Gamma, eqname : tau_1 = tau_2 tack e_2 : tau$ (d), and $Gamma tack tau ok$ (e).
  3. By induction (2.a), we have $theta(Gamma) tack e_1 : theta(tau')$.
  4. Since $fv(tau_1 = tau_2) disjoint theta$.
  5. By @subst-stable-lemma (2.b), $theta(Gamma) tack theta(forall ceil(tau_1 = tau_2 rigid)) <= theta(tau')$.
  6. By definition of substitution (4), $theta(forall ceil(tau_1 = tau_2 rigid)) = forall ceil(tau_1 = tau_2 rigid)$.
  7. By (5, 6), we have $theta(Gamma) tack forall ceil(tau_1 = tau_2 rigid) <= theta(tau')$.
  8. By (2.c) and definition of substituion, we have $eqname disjoint theta(Gamma)$.
  9. By induction (2.d), we have $theta(Gamma, eqname : tau_1 = tau_2) tack e_2 : theta(tau)$. By definition of substitution, we have $theta(Gamma, eqname : tau_1 = tau_2) =theta(Gamma), eqname : theta(tau_1) = theta(tau_2)$. By definition of substitution (4), $theta(tau_1) = tau_1$ and $theta(tau_2) = tau_2$. So we have $theta(Gamma), eqname : tau_1 = tau_2 tack e_2 : theta(tau)$.
  10. By @subst-stable-lemma (2.e), we have $theta(Gamma) tack theta(tau) ok$.
  11. We have $theta(Gamma) tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : theta(tau)$ by:
  $
    #proof-tree(
    prem-min-spacing: 10pt,
    rule(
      $theta(Gamma) tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : theta(tau)$,
      rule(
        $theta(Gamma) tack e_1 : theta(tau')$,
        $(3)$
      ),
      rule(
        $theta(Gamma) tack forall ceil(tau_1 = tau_2 rigid) <= theta(tau')$,
        $(7)$
      ),
      rule(
        $eqname disjoint theta(Gamma)$,
        $(8)$
      ),
      rule(
        $theta(Gamma), eqname: tau_1 = tau_2 tack e_2 : theta(tau)$,
        $(9)$
      ),
      rule(
        $theta(Gamma) tack theta(tau) ok$,
        $(10)$
      )
    )
  )
  $
]


_Monotonicity._ We can extend the instantiation relation $Gamma tack sigma <= sigma'$ to contexts $Gamma <= Gamma'$ as follows
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

== Explicit AML

TODO
