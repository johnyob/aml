#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

// HACK to get thm to left align
#show: thmrules

We define the constraint solver as a stack machine. Our machine is defined in terms of a transition relation on states of the form $(S, U, C)$, consisting of a stack $S$, a unification problem $U$, and an in-progress constraint $C$. 

#let sscope = $phi.alt$

_Stacks_. The stack $S$ represents the context in which $U and C$ appears. It contains the bindings for flexible and rigid type variables, scope variabls, term variables, and equation names, that may appear in $U and C$. 
Our states are closed, meaning $S$ must bind all free variables in $U and C$. 

#syntax(
  syntax-rule(
    name: [Frames], 
    $F$,
    $square and C |  exists alpha :: kappa. square | forall alpha :: kappa. square$, 
    $ clet x = forall overline(alpha :: kappa). lambda beta. square cin C$, 
    $ clet x = forall overline(alpha :: kappa). lambda beta. U cin square$, 
    $phi.alt : tau_1 = tau_2 => square
    $
  ), 


  syntax-rule(
    name: [Stacks], 
    $S$, 
    $emptyset | S :: F$
  ),
)
#let tformera = $op(tformer)^a$
#let sptformera = $space tformera$

// Holes
The stack additionally indicates how to continue after $C$ has been solved. The different forms of stack frames directly correspond to those constraints with at least one subconstraint. The overall stack can then be seen as a constraint with a hole in which $C$ is plugged.

_Unification Problems_.  Our constraints are eventually reduced to equations on first-order terms (solved under a mixed prefix). We express these reduced constraints as _unification problems_ $U$, which form a subset of constraints. We define _unification_ as a (non-deterministic) transition relation on _unification problems_. 


#let umultieq = $epsilon.alt$
#let umultilb = $eta$
#let umulti(phi, lb, eq) = $#phi tack #lb subset.eq #eq$
#syntax(
  syntax-rule(
    name: [Unification Problems], 
    $U$, 
    $ctrue | cfalse | U and U | exists alpha :: kappa. U | umultieq$), 

  syntax-rule(
    name: [Multi-equations], 
    $umultieq$, 
    $tau^kappa | umultieq = tau^kappa$
  ),

)


// Multi-equations 
Following Pottier and Remy, we replace ordinary binary atomic constraints such as equality $tau_1 = tau_2$ with _multi-equations_. Similarly, we replace binary equality
between scopes with multi-equations. The interpretation of both sorts of multi-equations is given by: 
$
  #proof-tree(
    rule(
      $kappa, phi, rho tack umultieq_Ty$, 
      $exists gt$, 
      $forall tau in umultieq. space phi(tau) = gt$, 
    )
  )
  #h1
  #proof-tree(
    rule(
      $kappa, phi, rho tack umultieq_Scope$, 
      $exists kappa'$, 
      $forall Psi in umultieq. space phi(Psi) = kappa'$
    )
  )
  #v2
  #proof-tree(
    rule(
      $Delta tack umultieq_Ty ok$, 
      $forall tau in umultieq_Ty.$,
      $Delta tack tau ok$
    )
  )
  #h1
  #proof-tree(
    rule(
      $Delta tack umultieq_Scope ok$,
      $forall Psi in umultieq_Scope.$, 
      $Delta tack Psi ok$
    )
  )
$
That is, $phi$ satisfies $umultieq$ if all members of $umultieq$ are mapped to a single value in the model by $phi$. 

// Solver contexts and well-formedness
#let srv = textsf("rv")
#let sfv = textsf("fv")
#let sv = textsf("sv")
#let seqs = textsf("eqs")
#let stmv = textsf("tmv")
#let styv = textsf("tyv")
#let sc = textsf("c")

_Well-formedness._ We write $srv(S)$, $sfv(S)$, $sv(S)$, and $seqs(S)$ for the rigid and flexible type variables, scope variables, and equation names in the stack $S$, respectively. 
We write $stmv(S)$ and $styv(S)$ for the term and type variables (flexible or rigid) bound in $S$, the latter is defined as $overline(srv(S) :: frigid), overline(sfv(S) :: fflex)$. 
We write $(dom(stmv(S)), styv(S), sv(S), seqs(S))$ for the context synthesized from $S$, denoted $sc(S)$. 

$
  srv(S) &= cases(
    dot &"if" S = dot, 
    srv(S')\, alpha &"if" S = S' :: forall alpha. square,
    srv(S')\, srv(Theta) &"if" S = S' :: clet x : cforall(Theta, square, tau) cin C, 
    srv(S') #h1&"otherwise" (S = S' :: \_)
  )

  #h1 
  sfv(S) &= cases(
    dot &"if" S = dot, 
    sfv(S')\, alpha &"if" S = S' :: exists alpha. square,
    sfv(S')\, sfv(Theta) &"if" S = S' :: clet x : cforall(Theta, square, tau) cin C, 
    sfv(S') #h1&"otherwise" (S = S' :: \_)
  ) 
$
$
  seqs(S) = cases(
    dot &"if" S = dot, 
    seqs(S')\, sscope &"if" S = S' :: sscope : A ==> square, 
    seqs(S') &"otherwise" (S = S' :: \_)
  )
  #h1
  sv(S) = cases(
    dot &"if" S = dot, 
    sv(S')\, scopev &"if" S = S' :: exists scopev. square, 
    sv(S')\, sv(Theta) &"if" S = S' :: clet x : cforall(Theta, square, tau) cin C,
    sv(S') &"otherwise" (S = S' :: \_)
  )
  #v2
  stmv(S) = cases(
    dot &"if" S = dot, 
    stmv(S')\, x : sigma #h1&"if" S = S' :: cdef x : sigma cin square, 
    &"or" S = S' :: clet x : sigma cin square, 
    stmv(S') &"otherwise" (S = S' :: \_)
  )
$

#judgement-box($tack S ok$)
$
  #proof-tree(
    rule(
      $tack dot ok$, 
      $$
    )
  )
  #h1
  #proof-tree(
    rule(
      $tack S :: exists alpha. square ok$, 
      $tack S ok$,
      $alpha disjoint styv(S)$, 
    )
  )
   #h1
   #proof-tree(
    rule(
      $tack S :: exists scopev. square ok$, 
      $tack S ok$,
      $scopev in.not sv(S)$, 
    )
  )
  #h1 
  #proof-tree(
    rule(
      $tack S :: forall alpha. square ok$, 
      $tack S ok$, 
      $alpha disjoint styv(S)$
    )
  )
  #v2 
  #proof-tree(
    rule(
      $tack S :: cdef x : sigma cin square ok$, 
      $tack S ok$, 
      $x in.not stmv(S)$, 
      $sc(S) tack sigma ok$
    )
  )
  #h1 
  #proof-tree(
    rule(
      $tack S :: clet x : cforall(Theta, square, tau) cin C ok$, 
      $tack S ok$, 
      $x in.not stmv(S)$,
      $sc(S), x tack C ok$
    )
  )
  #v2 
  #proof-tree(
    rule(
      $tack S :: clet x : hat(sigma) cin square ok$, 
      $tack S ok$, 
      $x in.not stmv(S)$, 
      $sc(S) tack hat(sigma) ok$
    )
  )
  #h1
  #proof-tree(
    rule(
      $tack S :: sscope : tau_1 = tau_2 ==> square ok$, 
      $tack S ok$, 
      $sscope in.not seqs(S)$, 
      $sc(S) tack tau_1 = tau_2 ok$, 
    )
  )
$

To check the well-formedness of constraints embedded in stack frames, the rules $tack S ok$ use the contexts induced by $S$. 
These judgements only ensure the term variables, type variables and named assumptions used in constraints are bound in $S$. 
In order for the state $(S, U, C)$ to be well-formed ($tack (S, U, C) ok$), we require that $S$ is well-formed ($tack S ok$), $U$ and $C$ are well-formed in $sc(S)$ ($sc(S) tack U and C ok$). 

// Ordering on assumptions

#let sminass = textsf("min-assm")


== Solver Rules 

We now introduce the rules of the constraint solver itself. 
The solver consists of a (non-deterministic) state rewriting system, given in Figure ??. We assume re-writings are performed modulo 
$alpha$-renaming and commutativity of conjunctions and multi-equations. 

A constraint is satisfiable in a given context if the solver reaches a state of the form ($cal(X), hat(U), ctrue$) where $cal(X)$ is an existential stack context and $hat(U)$ is a _satisfiable solved form_ of a unification problem from an initial configuration build from $C$ $(square, ctrue, C)$. From such a final state, we can read off a most general solution for the constraint by interpreting $hat(U)$ as a substitution. If the constraint is unsatisfiable, the solver reaches a state of the form $(S, cfalse, C)$. 


#let occurs = $op(textsf("occurs in"))$

_Unification_. 
#let sunify = $scripts(-->)_S$
The relation $U sunify U'$ describes the unification algorithm in the _context_ $S$; given in Figure ??. We often omit $S$ when it is unncessary.

_Notation._ We use the meta-variable $cal(v)$ to refer to a type or scope variable in a unification problem. We often additionally drop the $Ty$ and $Scope$ subscripts on multi-equations. 

We say $alpha occurs beta$ with respect to $U$ if $U$
contains a multi-equation of the form $tau = alpha = ...$ 
where $tau$ is a non-variable type satisfying $beta in fv(tau)$. 
A unification problem $U$ is cyclic if there exists $alpha$ such that $alpha occurs^* alpha$ wrt. $U$. 

A _solved form_ $hat(U)$ is either $cfalse$ or $exists overline(cal(v)). and.big_i epsilon.alt_i$ where 
every multi-equation contains at most one non-variable structure, no two multi-equations share a variable, and $hat(U)$ is not cyclic.  Similarly, a _solved scheme_ $hat(sigma)$ is a constrainted type scheme of the form $cforall(Theta, hat(U), alpha)$.

#comment[TODO: explain unification rules]

$
  // Common rules
  (exists cal(v). U_1) and U_2 &--> exists cal(v). U_1 and U_2 &#h(2cm)&"if" cal(v) \# U_2 \ 
  U &--> cfalse 
  &&"if" U "is cyclic" \ 
  cal(U)[cfalse] &--> cfalse \
  cal(U)[U] &--> cal(U)[U']  
  &&"if" U --> U' \ 
  U and ctrue &--> U \ 

  // Merge rule 
  cal(v) = umultieq_1 and cal(v) = umultieq_2 &--> cal(v) = umultieq_1 = umultieq_2  \ 

  // Normalize rules  
  cal(v) = cal(v) = umultieq &--> cal(v) = umultieq \ 

  // Shallowify
  overline(tau)[tau_i] tformer = umultieq  &--> exists alpha. overline(tau)[alpha] tformer = umultieq and alpha = tau_i &&"if" tau_i in.not varset(Ty) and alpha disjoint overline(tau), umultieq \ 

  [Psi]tau = umultieq &--> exists scopev. [scopev]tau = umultieq and scopev = Psi &&"if" Psi in.not varset(Scope) and scopev disjoint Psi, tau, umultieq \

  // Decomposition types 
  overline(alpha) tformer = overline(beta) tformer = umultieq &--> overline(alpha) tformer = umultieq and overline(alpha) = overline(beta) \ 

  // Clash 
  overline(alpha) tformer = overline(beta) tformerg = umultieq &sunify exists scopev. overline(alpha) tformer = umultieq and overline(alpha) = overline([scopev]tau) and overline(beta) = overline([scopev]tau') and S; scopev tack overline(tau) tformer equiv overline(tau') tformerg &&"if" tformer != tformerg \ 

  // Scope dist + compat
  [scopev]tau = overline(alpha) tformer = umultieq &sunify overline(alpha) tformer = umultieq and overline(alpha) = overline([scopev]tau'') and S; scopev tack overline(tau'') tformer equiv tau \

  // Scope eq 
  [scopev_1]tau_1 = [scopev_2]tau_2 = umultieq &sunify [scopev_1]tau_1 = umultieq and scopev_1 = scopev_2 and S; scopev_1 tack tau_1 equiv tau_2 \ 

  // Scope equalities 
  Psi, eqname = umultieq &--> exists scopev. scopev, eqname = umultieq and scopev = Psi\

  scopev, eqname = Psi_2, eqname = umultieq &--> scopev, eqname = umultieq and scopev = Psi_2 \ 

  scopev, eqname_1 = Psi_2, eqname_2 = umultieq &--> (exists rho.alt. scopev = rho.alt, eqname_2 and Psi_2 = rho.alt, eqname_1) and scopev, eqname_1 = umultieq 
$

We write $S; scopev tack tau_1 equiv tau_2$ for finding the minimum set of equations $overline(eqname)$ in $S$ s.t $tau_1 equiv tau_2$ and adding the constraint $exists rho.alt. scopev = rho.alt, overline(eqname)$.

Minimum is minimal in the level of the implication -- i.e. pick youngest equations first if given an option. 

_Solver._ 


$
(S, U, C) &--> (S, U', C) &#h(2cm)&"if" U --> U' \ 
 (S, U, tau_1 = tau_2) &--> (S, U and tau_1 = tau_2, ctrue) \ 
 (S, U, Psi_1 = Psi_2) &--> (S, U and Psi_1 = Psi_2, ctrue) \
 (S, U, C_1 and C_2) &--> (S :: square and C_2, U, C_1) \ 
 (S, U, exists alpha. C) &--> (S :: exists alpha. square, U, C) &#h(2cm)&"if" alpha \# U \ 
 (S, U, exists scopev. C) &--> (S :: exists scopev. square, U, C) \
 (S, U, forall alpha. C) &--> (S :: forall alpha. square, U, C) \
 (S, U, cdef x : sigma cin C) &--> (S :: cdef x : sigma cin square, U, C) \ 
 (S, U, x <= tau) &--> (S, U, sigma <= tau) &&"if" x : sigma in stmv(S) \ 
 (S, U, (cforall(Theta, C, tau')) <= tau) &--> (S, U, exists Theta. C and tau = tau')\
 (S, U, clet x : cforall(Theta, C_1, tau) cin C_2) &--> (S :: clet x : cforall(Theta,  square, tau) cin C_2, U, C_1) \
 (S, U, eqname : tau_1 = tau_2 ==> C) &--> (S :: eqname : tau_1 = tau_2 ==> square, U, C)
$





Existential extraction rules are:
$
  (S, exists cal(v). U, C) &--> (S :: exists cal(v). square, U, C) \ 
  &"if" cal(v) \#C \ 
  (S :: square and C_1 :: exists overline(cal(v)). square, U, C_2) &--> (S :: exists overline(cal(v)). square :: square and C_1, U, C_2) \ 
  &"if" cal(v) \# C_1 \
  (S :: cdef x : sigma cin square :: exists overline(cal(v)). square, U, C) &--> (S :: exists overline(cal(v)). square :: cdef x : sigma cin square, U, C) \ 
  &"if" cal(v) \# sigma \
  (S :: clet x : cforall(Theta, square, tau) cin C' :: exists overline(cal(v)). square, U, C) &--> (S :: clet x :: cforall((Theta, overline(cal(v))), square, tau) cin C', U, C) \ 
  &"if" overline(cal(v)) disjoint C \
  (S :: clet x : hat(sigma) cin square :: exists overline(cal(v)). square, U, C) &--> (S :: exists overline(cal(v)). square :: clet x : hat(sigma) cin square, U, C) \ 
  &"if" overline(cal(v)) disjoint hat(sigma) \
  (S :: clet x : cforall((Theta, overline(cal(v))), square, alpha) cin C, U, ctrue) &--> (S :: exists overline(cal(v)). square :: clet x : cforall(Theta, square, alpha) cin C, U, ctrue) \
  &"if" overline(cal(v)) disjoint C and (seqs(S) ==> exists Theta. U) "determines" overline(cal(v)) \
  (S :: forall alpha. square :: exists overline(cal(v))_1, overline(cal(v))_2. square, U, ctrue) &--> (S :: exists overline(cal(v))_1. square :: forall alpha. square :: exists overline(cal(v))_2. square, U, ctrue) \ 
  &"if" overline(cal(v)_1) disjoint alpha and (seqs(S) ==> exists alpha, overline(cal(v))_2. U) "determines" overline(cal(v))_2 \

  (S :: eqname : tau_1 = tau_2 ==> square :: exists overline(cal(v)_1), overline(cal(v)_2). square, U, ctrue) &--> (S :: exists overline(cal(v)_1). square :: eqname : tau_1 = tau_2 ==> square :: exists overline(cal(v)_2). square, U, C ) \ 
  &"if" (seqs(S) ==> exists overline(cal(v)_2). U) "determines" overline(cal(v)_1) 

$
Pop rules:
$
  
  (S :: square and C, U, ctrue) &--> (S, U, C) \ 
  (S :: clet x : cforall(Theta, square, alpha) cin C, U_1 and U_2, ctrue)  &--> (S :: clet x : safe(cforall(Theta, U_2, alpha)) cin square, U_1, C) \
  &"if" Theta disjoint U_1 and (seqs(S) ==> exists Theta. U_2) equiv ctrue \ 

  (S :: clet x : hat(sigma) cin square, U, ctrue) &--> (S, U, ctrue) \ 

  (S :: forall alpha. square :: exists overline(cal(v)). square, U_1 and U_2, ctrue) &--> (S, U_1, ctrue) \ 
  &"if" alpha, overline(cal(v)) disjoint U_1 and (seqs(S) ==> exists overline(cal(v)). U_2) equiv ctrue \ 

  (S :: eqname : tau_1 = tau_2 ==> square :: exists overline(cal(v)). square, U_1 and U_2, ctrue) &--> (S, U_1, ctrue) \ 
  &"if" eqname, overline(cal(v)) disjoint U_1 and (seqs(S), eqname:tau_1 = tau_2 ==> exists overline(cal(v)). U_2) equiv ctrue \ 
$
Adminstrative:
$
  &(S :: clet x : cforall(Theta, square, tau) cin C, U, ctrue) \ 
  &--> (S :: clet x : cforall((Theta, alpha :: fflex), square, alpha), U and alpha = tau, ctrue) \ 
  & "if" alpha disjoint U, tau and tau in.not varset(Ty) \ \ \

  &(S :: clet x :: cforall((Theta, cal(v)), square, alpha) cin C, cal(v) = cal(v') = umultieq and U, ctrue) \
  &--> (S :: clet x : cforall((Theta, cal(v)), square, theta(alpha)) cin C, cal(v) and cal(v') = theta(umultieq) and theta(U), ctrue) \ 
  &"if" cal(v) != cal(v') and theta = [cal(v) |-> cal(v')] \ \ \ 

  &(S :: clet x : cforall((Theta, cal(v)), square, alpha) cin C, cal(v) = umultieq and U, ctrue ) \ 
  &--> (S :: clet x : cforall(Theta, square, alpha) cin C, umultieq and U, ctrue) \ 
  &"if" cal(v) disjoint alpha, umultieq, U \ \ \ 
$

Fail:
$
  // Escape 
  (S :: forall alpha. square :: exists overline(cal(v)). square, U, ctrue) &--> cfalse \ 
  & "if" alpha disjoint overline(cal(v)) and beta occurs^* alpha and beta disjoint alpha, cal(v) \ 

  // Unified to something 
  (S :: forall alpha. square :: exists overline(cal(v)). square, alpha = tau = umultieq and U, ctrue) &--> cfalse \ 
  &"if" alpha disjoint overline(cal(v)) and tau in.not varset(Ty) \ 

  // Scope escape 

  (S :: eqname : tau_1 = tau_2 ==> square :: exists overline(cal(v)). square, U and umultieq_Scope, ctrue) &--> cfalse \ 
  &"if" eqname in umultieq_Scope and (seqs(S), eqname: tau_1 = tau_2  ==> exists overline(cal(v)). umultieq_Scope) equiv.not ctrue 

$

We define (informally for now -- will make this formal on Thursday 20th Feb) $safe(cforall(Theta, U, alpha))$ as a type scheme $cforall(Theta, U and U_safe, alpha)$
where $U_safe$ is a conjunction of scope equalities $and.big_i scopev_i = dot$ for any scope variable $scopev$ that may make 
a rigid variable $beta :: frigid in Theta$ dangerous -- this can be determined by looking at all scoped types $[scopev]tau$ in $U$ that $alpha$ dominates 
and adding $scopev = dot$ if $beta in fv(tau)$.  



== Metatheory 

// We now prove the existence of principal types by providing an algorithm that succeeds in finding one, or fails when the expression 
// is ill-typed.

// #definition[
//   A type scheme $sigma$ is said to be _principal_ of an #aml expression $e$ in $Gamma$ if
//   + $Gamma tack e : sigma$
//   + For any other type scheme $sigma'$, if $Gamma tack e : sigma'$ then $Gamma tack sigma <= sigma'$ 
// ]


// A solved form of a unification problem, denoted $hat(U)$, is a unification problem of the form $exists overline(alpha), overline(scopev). and.big_i beta_i = tau_i and and.big_j rho.alt_j = Psi_j$ and $overline(beta) disjoint fv(overline(tau)), overline(rho.alt) disjoint fv(overline(Psi))$. 

// A solved form is said to be _canonical_ when $fv(overline(tau), overline(Psi)) subset.eq overline(alpha), overline(scopev)$ and $overline(alpha), overline(scopev) disjoint overline(beta), overline(rho.alt)$ (i.e. the free variables are exactly $overline(alpha), overline(rho.alt)$). 

// #definition[
//   Let $theta$ be an _idempotent_ substitution of domain $overline(alpha), overline(scopev)$. We write $exists theta$ for the canonical solved form $exists rng(theta). and.big_i alpha_i = theta(alpha_i) and and.big_j scopev_j = theta(scopev_j)$. 
  
//   - We say $theta$ is a _unifier_ of $U$ if and only if $exists theta tack.double U$. 

//   - We say $theta$ is _the most general unifier_ of $U$ if and only if $exists theta equiv U$. 
// ]

