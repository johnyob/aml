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
    collection: $Exp$, 
    $e$, 
    $x | efun x -> e | e space e$, 
    $elet x = e ein e | efun (etype alpha) -> e | (e : tau)$, 
    $erefl | ematch e : tau = tau ewith erefl -> e$,
  ),
)

#aml extends #ml expressions, variables, functions and let expressions are standard. #aml introduces an explicit universal quantifier $efun (etype alpha) -> e$, equivalent to System #textsf("F")'s $Lambda alpha. e$. The constructor $erefl$ has the type $tau = tau$. The $ematch e : tau_1 = tau_2 ewith erefl -> e'$ construct introduces the type-level equality in $e'$ as a _local constraint_ using the proof $e$.


_Notation_. We write $overline(e)$ for a (possible empty) set of elements ${e_1, ..., e_n}$ and a (possibly empty) sequence $e_1, ..., e_n$. The interpretation of whether $overline(e)$ is a set or a sequence is often implicit. We write $overline(e_1) disjoint overline(e_2)$ as a shorthand for when $overline(e_1) sect overline(e_2) = emptyset$. We write $overline(e_1), overline(e_2)$ as the union or concatenation (depending on the interpretation) of $overline(e_1)$ and $overline(e_2)$. We often write $e$ for the singleton set (or sequence).

_Types_. The syntax of types is as follows:
#syntax(
  collection-rule(
    name: [Type Variables], 
    $varset(Ty)$, 
    $alpha, beta, gamma, scopev, rho.alt$
  ),
  collection-rule(
    name: [Equation Names], 
    $varset(EqName)$,
    $eqname$, 
  ), 
  syntax-rule(
    name: [Type Constructors], 
    collection: TyCon, 
    $tformer$, 
    $dot arrow dot | dot = dot | tunit$
  ),
  syntax-rule(
    name: [Types], 
    collection: $Ty$, 
    $tau^kappa$, 
    $alpha^kappa | overline(tau^ty) tformer | [tau^scope] tau | emptyset^scope | tau^scope, eqname$
  ),
  syntax-rule(
    name: [Type Schemes], 
    collection: Scm, 
    $sigma$, 
    $tau | tforall(alpha :: kappa) sigma$
  ), 
  syntax-rule(
    name: [Kinds], 
    collection: Kind, 
    $kappa$,
    $ty | scope$
  ),
  syntax-rule(
    name: [Flexibility], 
    collection: Flex, 
    $phi$, 
    $fflex | frigid$
  ),
  syntax-rule(
    name: [Contexts],
    collection: Ctx, 
    $Gamma$,
    $emptyset | Gamma, alpha ::^phi kappa | Gamma, eqname : tau = tau | Gamma, x: sigma$,
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
A scope is defined by a _row_ of equation names. An scope is either empty $emptyset$, a polymorphic scope variable $scopev$, or an extension of a scope $Psi$ with an equation $eqname$, written as $Psi, eqname$. Unlike many other applications of row polymorphism, we _do_ allow duplicate equation names, meaning that $eqname, eqname$ is _well-formed_ (though not equal to the scope $eqname$). However, our use of rows is primarily to represent sets of equations and ensure _coherence_, so these duplicates do not pose a problem.  

// Schemes
Polymorphic types are defined by _type schemes_ in a mostly typical #ml fashion, generalzing over zero or more variables. However, we extend the notion of polymorphism to also quantify over _scope variables_ as well, introducing a form of _scope polymorphism_.

// Contexts
Contexts bind term variables to type schemes, introduce (polymorphic) type and scope variables, and store (named) type equations $eqname: tau = tau'$. 
Contexts are ordered and duplicates are disallowed. We write $Gamma, Gamma'$ for the concatenation of two contexts (assuming disjointness holds). We write $dom(Gamma)$ for the _domain_ of the context, which informally represents the set of type and scope variables, term variables and equation names. We often write $overline(e) disjoint Gamma$ as a shorthand for $overline(e) disjoint dom(Gamma)$.

// Flexibility 
Each type variable bound in the context is associated with a _flexibility_ makrer $phi$ which can either be _rigid_ ($frigid$) or _flexible_ ($fflex$). A variable is marked _rigid_ if introduced by an explicit quantifier $efun (etype alpha) -> e$, and _flexible_ if introduced implicitly by generalization. The distinction serves two purposes. First, it identifies explicitly introduced type variables, which we leverage to ensure annotations only make reference to such variables. The second purpose we explain below in our definition of well-formedness. Second, flexibility plays a key role in our well-formedness relation for _scoped ambivalent types_, which we elaborate on later. 

We assume types, scopes, and type schemes are equivalent modulo $alpha$-renaming. The definition for the set of free variables on types and schemes is standard.

$
  fv (alpha) &= { alpha } &&& fv (emptyset) &= emptyset \
  fv (overline(tau) tformer) &= union.big_i fv (tau_i) &&& fv (Psi, eqname) &= fv (Psi) \
  fv ([Psi] tau) &= fv (Psi) union fv (tau) &#h(2cm)&&  fv(tforall(alpha :: kappa) sigma) &= fv(sigma) \\ { alpha } \  \
$



_Well-formedness_. Well-formedness for types, type schemes and contexts is mostly standard: ensuring types are well-kinded, prevent duplicate bindings in contexts, and enforce correct scoping of type variables. 

However, our well-formedness judgements for types, written $Gamma tack tau^kappa :: kappa space phi$, additionally tracks the flexibility 
$phi$ of the type. Tracking flexibility allows us to introduce two restrictions inspired by Garrigue and Rémy's work on ambivalent types:
1. Only equations between _rigid_ types can be introduced to the context.
2. In a scoped ambivalent type $[Psi]tau$, the type $tau$ _under_ the scope $Psi$ must be rigid. 
These restrictions also simply our presentation while remaining sufficient to encode OCaml's behaviour. For convenience, we write 
$Gamma tack tau^kappa :: kappa$ when the type is flexible. The $phi_1 <= phi_2$ relation is used to weaken the flexibility of variables, permitting the following rule 
to be derivable (Lemma ??):
$
  #proof-tree(
    rule(
      $Gamma tack tau^kappa :: kappa space phi_2$, 
      $Gamma tack tau^kappa :: kappa space phi_1$, 
      $phi_1 <= phi_2$
    )
  )
$ 

#judgement-box($phi_1 <= phi_2$, $Gamma tack tau^kappa :: kappa space phi$, $Gamma tack sigma scm$, $Gamma ctx$)

$

  #proof-tree(
    rule(
      $phi <= phi$, 
      name: [$<=$FlexRefl]
    )
  )

  #h1 
  

  #proof-tree(
    rule(
      $frigid <= fflex$, 
      name: [$<=$FlexWeaken]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack alpha :: kappa space phi'$,
      $alpha ::^phi kappa in Gamma$, 
      $phi <= phi'$, 
      name: [VarWF]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(tau) tformer :: ty phi$,
      $forall i, space Gamma tack tau_i :: ty phi$, 
      name: [TyConWF]
    )
  )

  #v2


  #proof-tree(
    rule(
      $Gamma tack [Psi] tau :: ty$,
      $Gamma tack Psi :: scope$,
      $Gamma tack tau :: ty frigid$, 
      name: [AmbWF]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack emptyset :: scope$,
      $$, 
      name: [EmpScWF]
    )
  )

  #v2


  #proof-tree(
    rule(
      $Gamma tack Psi, eqname :: scope$,
      $Gamma tack Psi :: scope$,
      $eqname in dom(Gamma)$, 
      name: [ConsScWF]
    )
  )


  #h1

  #proof-tree(
    rule(
      $Gamma tack tau scm$, 
      $Gamma tack tau :: ty$, 
      name: [ScmTy]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma tack tforall(alpha :: kappa) sigma scm$,
      $Gamma, alpha ::^phi kappa tack sigma scm$,
      $alpha disjoint Gamma$, 
      name: [Scm$forall$]
    )
  )


  #v2

  #proof-tree(
   rule(
      $emptyset ctx$,
      $$, 
      name: [EmpCtx]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, alpha ::^phi kappa ctx$,
      $Gamma ctx$,
      $alpha disjoint Gamma$, 
      name: [TyVarCtx]
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Gamma, x : sigma ctx$,
      $Gamma ctx$,
      $Gamma tack sigma scm$,
      $x disjoint Gamma$, 
      name: [VarCtx]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Gamma, eqname: tau_1 = tau_2 ctx$,
      $Gamma ctx$,
      $Gamma tack tau_1 :: ty frigid$,
      $Gamma tack tau_2 :: ty frigid$,
      $eqname disjoint Gamma$, 
      name: [EqCtx]
    )
  )
$


_Type Equivalence._ Types have an associated equivalence relation, written $Gamma tack tau_1 equiv tau_2 space [Psi]$, read: _under the context $Gamma$, $tau_1$ and $tau_2$ are equivalent in the scope $Psi$_. We refer to $Psi$ as the _support_ in the equivalence relation. We often write $Gamma tack tau_1 equiv tau_2$ if the support is empty. 

To prove equivalences, we can rely on equalities referenced in $Psi$ as well as standard rules such as reflexivity, symmetry, transitivity, congruence, and decomposition. Type constructors are injective. Additionally, we introduce three rules associated with scoped ambivalent types. 

The first rule permits us to prove equivalences between scoped types using the equations in their scopes. 
The latter two rules are axioms: distributivity and $M$. Distributivity allows the movement of scopes within a type, which is cruicial for ensuring that eliminators can be applied correctly. However, as explained above, we do not permit the concatentation of scopes with distributivity. Axiom $M$ allows us to remove trivial scopes.  


#judgement-box($Gamma tack tau_1 equiv tau_2 space [Psi]$)
$
  #proof-tree(
    rule(
      $Gamma tack tau equiv tau space [Psi]$,
      $Gamma tack tau :: ty$, 
      name: [$equiv$Refl]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_1 equiv tau_2 space [Psi]$,
      $Gamma tack tau_2 equiv tau_1 space [Psi]$, 
      name: [$equiv$Sym]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack tau_1 equiv tau_3 space [Psi]$,
      $Gamma tack tau_1 equiv tau_2 space [Psi]$,
      $Gamma tack tau_2 equiv tau_3 space [Psi]$, 
      name: [$equiv$Trans]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_1 equiv tau_2 space [Psi]$,
      $eqname : tau_1 = tau_2 in Gamma$,
      $eqname in Psi$, 
      name: [$equiv$Use]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack overline(tau_1) tformer equiv overline(tau_2) tformer space [Psi]$,
      $forall i, space Gamma tack tau_(1i)  equiv tau_(2i) space [Psi]$, 
      name: [$equiv$Cong]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_(1i) equiv tau_(2i) space [Psi]$,
      $Gamma tack overline(tau_1) tformer equiv overline(tau_2) tformer space [Psi]$, 
      name: [$equiv$Inj]
    )
  ) 

  #v2 

  #proof-tree(
    rule(
      $Gamma tack [Psi_1]tau_1 equiv [Psi_1]tau_2 space [Psi_2]$, 
      $Gamma tack tau_1 equiv tau_2 space [Psi_1]$, 
      name: [$equiv$Amb]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack [Psi_1](overline(tau) tformer) equiv overline([Psi_1]tau) tformer space [Psi_2]$, 
      $arity(tformer) > 0$, 
      name: [$equiv$Dist]
    )
  )


  #v2 

  #proof-tree(
    rule(
      $Gamma tack [emptyset]tau equiv tau space [Psi]$, 
      $Gamma tack tau :: ty frigid$, 
      name: [$equiv$$M$]
    )
  )
$


_Typing Judgements_. #aml typing judgements have the form $Gamma tack.r e: sigma$ stating that $e$ has the type (scheme) $sigma$ in the context $Gamma$.
We assume well-formedness for contexts $Gamma ctx$. The typing rules are given below.


#judgement-box($Gamma tack e : sigma$)
$
  #proof-tree(
    rule(
      $Gamma tack x : sigma$,
      $x : sigma in Gamma$, 
      name: [Var]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun x -> e : tau_1 -> tau_2$,
      $Gamma, x : tau_1 tack e : tau_2$,
      $Gamma tack tau_1 :: ty$, 
      name: [Fun]
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma tack e_1 space e_2 : tau_2$,
      $Gamma tack e_1 : tau_1 -> tau_2$,
      $Gamma tack e_2 : tau_1$,
      name: [App]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : sigma_2$,
      $Gamma tack e_1 : sigma_1$,
      $Gamma, x : sigma_1 tack e_2 : sigma_2$, 
      name: [Let]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e : tforall(alpha :: kappa) sigma$,
      $Gamma, alpha ::^fflex kappa tack e : sigma$,
      $alpha disjoint Gamma$,
      name: [Gen]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun (etype alpha) -> e : tforall(alpha :: ty) sigma$,
      $Gamma, alpha ::^frigid ty tack e : sigma$,
      $alpha disjoint Gamma$,
      $alpha in.not dangerous(sigma)$, 
      name: [TyFun]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau_2$,
      $Gamma tack e : tau_1$,
      $Gamma tack tau :: ty frigid$,
      $Gamma tack forall ceil(tau) <= tau_1, tau_2$,
      name: [Annot]
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Gamma tack e : sigma'$,
      $Gamma tack e : sigma$,
      $Gamma tack sigma <= sigma'$,
      name: [Sub]
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma tack ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2 : sigma$,
      $Gamma tack (e_1 : tau_1 = tau_2) : \_$,
      $eqname disjoint Gamma$,
      $Gamma, eqname : tau_1 = tau_2 tack e_2 : sigma$,
      $Gamma tack sigma scm$,
      name: [Match]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : tforall(alpha :: ty) alpha = alpha$,
      $$, 
      name: [Refl]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack () : tforall(scopev :: scope) [scopev]tunit$,
      $$, 
      name: [Unit]
    )
  )

$

_Variables_. Variables $(x)$ are typed as usual. If a variable has a polymorphic type, the standard #ml instantiation rule applies. The instantiation relation $Gamma tack sigma <= sigma'$ is defined as follows:
$
  #proof-tree(
    rule(
      $Gamma tack tau <= tau'$,
      $Gamma tack tau equiv tau'$, 
      name: [$<=equiv$]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tforall(alpha :: kappa) sigma <= sigma'$,
      $Gamma tack tau^kappa :: kappa$,
      $Gamma tack sigma[alpha := tau^kappa] <= sigma'$, 
      name: [$<=forall$L]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack sigma <= tforall(alpha :: kappa) sigma'$,
      $Gamma, alpha ::^fflex kappa tack sigma <= sigma'$,
      $alpha disjoint Gamma$,
      name: [$<=forall$R]
    )
  )
$

This relation is mostly standard, adapted to account for type equivalence and scope polymorphism.
An interesting consequence of our instantiation relation is that the following rule is derivable in #aml:
$
  #proof-tree(
  rule(
    $Gamma tack e : tau'$,
    $Gamma tack e : tau$,
    $Gamma tack tau equiv tau'$, 
    name: [Equiv]
  )
)
$
This rule plays a crucial role in manipulating scopes in our typing judgements.

_Equalities_. A type-level equality may be introduced via reflexivity using the unique constructor $erefl$ with type scheme $tforall(alpha) alpha = alpha$.
Pattern matching on equalities using $ematch e_1 : tau_1 = tau_2 ewith erefl -> e_2$ can eliminate the equality witness $e_1$ of type $tau_1 = tau_2$, adding it as an implicit equality to the context $Gamma$ while type checking the body $e_2$; the witness $e_1$ must have the structure of $tau_1 = tau_2$ but may have additional scopes -- we formalize this using annotations, as discussed below. Since the equation is only available in the scope of $e_2$, it must not be present in the return type $sigma$. We ensure this by allocating a fresh name for the equality $eqname disjoint Gamma$ and ensuring $eqname$ does not occur in $sigma$, this is done so by using the well-formedness judgement $Gamma tack sigma scm$.
If the return type fails to satisfy this condition, then we say the _equation ($eqname$) has escaped its scope_.

_Annotations_. Annotations represent an explicit loss of sharing of scopes between types. This loss of sharing of scopes permits us to eliminate ambivalence in our return type, thereby preventing scope escapes. The types $tau_1, tau_2$ need not be identical to $tau$ but must instead be _consistent instances_ of $tau$ with differing scopes. We express this by defining a _scope insertion_ function $ceil(tau)$ for rigid types, which produces a context of scope variables $cal(S)$ and a type $tau'$ with scopes inserted at _leaves_ of the type. Scopes at inner nodes can be inferred via the distributivity of scopes.
#let ceilret(a, b) = $#a triangle.r.small #b$
#[
#show math.equation: set align(end)
$
  ceil(alpha ) &= ceilret(scopev, [scopev]alpha) &&"fresh" scopev \
  ceil(tformer ) &= ceilret(scopev, [scopev]tformer) &&"fresh" scopev \
  ceil(overline(tau) tformer ) &= ceilret(#[$cal(S)_1, ..., cal(S)_n$], overline(tau')) tformer &#h(2.3cm)&"where" ceil(tau_i ) = ceilret(cal(S)_i, tau'_i)
$
]
We write $forall ceil(tau )$ for $tforall(cal(S)) tau'$ where $ceil(tau ) = ceilret(cal(S), tau')$. This type scheme describes a set of instances that are equivalent to $tau$ after erasing their scopes. We say such instances are _consistent instances_ of $tau$. 


_Functions_. Function applications $e_1 space e_2$ are standard and oblivious to scopes.
The parameter type $tau_1$ of the function $e_1$ must be equal to that of the argument $e_2$. In particular,
in the presence of scopes, if $e_1$ have the type $[Psi]tau$ where $tau$ and $Gamma; Psi tack tau equiv tau_1 -> tau_2$,
then the argument $e_2$ must have the type $[Psi]tau_1$ and the result of the application has the type $[Psi]tau_2$.
This behaviour matches the propagation of scopes for application in the following example:
```ocaml
let propagate_scope (type a) (w : (a, int -> int) eq) (f : a) =
  match w with Refl (* a = int -> int *) ->
  f 1
```
Naming `a = int -> int` as $eqname$, the result has the type $[eqname]tint$. This escapes the scope of the `match` expression, resulting in the following error (with `-principal` enabled):
```
Error: This expression has type int but an expression was expected of type 'a
       This instance of int is ambiguous:
       it would escape the scope of its equation
```

Functions $efun x -> e$ are standard, binding monomorphic types to $x$ in the body of $e$. The annotated form $efun (x : tau) -> e$ is syntactic sugar for $efun x -> elet x = (x : tau) cin e$, permitting _scope polymorphic_ types to be bound to $x$ in $e$. The use of scope polymorphism is cruicial to avoid scope escape errors when using $x$ in a context with a scope. For example, if `f` was not annotated with `(_ : a)` in the above example, then a scope escape would occur even if the return type was annotated. This is because the type of `f` would have to match $[eqname]tint$, thus leaking the equation $eqname$.


_Let Bindings and Generalization_. Let bindings $elet x = e_1 ein e_2$ assign a polymorphic type $sigma_1$ to $x$ in the scope of $e_2$. Generalizing the type of an expression using _flexible_ variables is standard.

Generalization using _rigid_ variables with an explicit quantifier $efun (etype alpha) -> e$ requires the _rigid_ generalizable variable $alpha$ cannot occur in 'dangerous' positions in the type scheme. A dangerous position is one that is under a (non-trivial #footnote([All trivial scopes may be removed using equivalence])) scope. We formally define this as follows:
$
  dangerous(alpha) &= emptyset \
  dangerous(overline(tau) tformer) &= union.big_i dangerous(tau_i) \
  dangerous([Psi]tau) &= fv(tau) \
  dangerous(tforall(alpha :: kappa) sigma) &= dangerous(sigma) \\ {alpha} \
$
This is because #aml has unrestricted instaniation (and type schemes), thus permitting a generalizable rigid variable under a non-trivial scope would result in a well-formedness
issue since scoped ambivalent types $[Psi]tau$ are only well-formed if $tau$ is _rigid_.

Additionally, without this condition, a loss in principality could occur. We demonstrate this by first considering the type of `coerce`, defined below:
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
It is interesting to note that the type is not more general by permitting a scope on the equality since $[scopev_5]([scopev_1]alpha = [scopev_2]beta) equiv [scopev_5, scopev_1]alpha = [scopev_5, scopev_2]beta$. The issue with this inferred type is that the additional scopes lose some of the sharing that Garrigue and Rémy's system enforces. This could result in some morally ambivalent programs being well-typed in our system. For example:
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

== Metatheory <aml-meta>

_Syntax-directed Typing Judgements._ As a first step towards type inference, we now present a _syntax-directed_ variant of #aml in Figure ??. It is useful to have a syntax-directed presentation to admit inversion rules solely on the structure of $e$. This technique is entirely standard [??]. 

Effectively, we removed the (Sub) and (Gen) rules, and always apply instantiation for variables and primitives and always generalize at let-bindings. 
We write $cal(V)$ for a sequence of non-rigid generalizable variables $overline(alpha ::^fflex kappa)$ used in (Let). Rather than inlining subsumption (as is standard), we keep it explicit, since each inlining would produce an explicit $equiv$-equivalence, which does not improve readability. 

#judgement-box($Gamma sdtack e : tau$)

$
  #proof-tree(
    rule(
      $Gamma sdtack x : tau$,
      $x : sigma in Gamma$,
      $Gamma tack sigma <= tau$, 
      name: [Var]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma sdtack efun x -> e : tau_1 -> tau_2$,
      $Gamma, x : tau_1 sdtack e : tau_2$,
      $Gamma sdtack tau_1 :: ty$, 
      name: [Fun]
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma sdtack e_1 space e_2 : tau_2$,
      $Gamma sdtack e_1 : tau_1 -> tau_2$,
      $Gamma sdtack e_2 : tau_1$,
      name: [App]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma sdtack elet x = e_1 ein e_2 : tau_2$,
      $Gamma, cal(V) sdtack e_1 : tau_1$,
      $cal(V) disjoint Gamma$,
      $Gamma, x : forall cal(V).tau_1 sdtack e_2 : tau_2$, 
      name: [Let]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma sdtack efun (etype alpha) -> e : tau'$,
      $Gamma, alpha ::^frigid ty sdtack e : tau$,
      $alpha disjoint Gamma$,
      $alpha in.not dangerous(tau)$,
      $Gamma tack tforall(alpha :: ty) tau <= tau'$, 
      name: [TyFun]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma sdtack (e : tau) : tau_2$,
      $Gamma sdtack e : tau_1$,
      $Gamma tack forall ceil(tau) <= tau_1, tau_2$,
      name: [Annot]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma sdtack erefl : tau$,
      $Gamma tack tforall(alpha :: ty) alpha = alpha <=  tau$, 
      name: [Refl]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma sdtack () : tau$,
      $Gamma tack tforall(scopev :: scope) [scopev]tunit <= tau$, 
      name: [Unit]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma sdtack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : tau$,
      $Gamma sdtack (e_1 : tau_1 = tau_2) : \_$,
      $eqname disjoint Gamma$,
      $Gamma, eqname : tau_1 = tau_2 sdtack e_2 : tau$,
      $Gamma tack tau ok$,
      name: [Match]
    )
  )
$


The syntax-directed presentation is sound and complete with respect to the declarative rules. 
The statements are almost entirely standard with the exception that our statement for completeness must explicitly reason about a set of generalizable variables.  

#theorem[_Soundness of the syntax-directed #aml typing judgements_][
  When $Gamma sdtack e : tau$ then we also have $Gamma tack e : tau$.
]

#theorem[_Completeness of the syntax-directed #aml typing judgements_][
  When $Gamma tack e : sigma$, then for some $cal(V) disjoint Gamma$, we also have $Gamma, cal(V) sdtack e : tau$ where $Gamma tack tforall(cal(V)) tau <= sigma$.
]

Having established that any typing derivable in the syntax-directed #aml type system is derivable in the declarative #aml type system (and vice versa), we henceforth use the
syntax-directed type system (implicitly).

#aml also enjoys several standard properties, including weakening, exchange, substitution, and well-formedness. 

_Monotonicity._ This property asserts that strengthening the type of a free term variable by making it more general preserves well-typedness. We draw the reader's attention to this property because Garrigue and Rémy identify it as key feature of their calculus. 


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



#theorem[_Monotonicity of #aml typing judgements_][
  If $Gamma tack e : tau$ holds and $Gamma' <= Gamma$, then $Gamma' tack e : tau$ holds.
] 


Detailed proofs of these properties are provided in the appendix. 
