
#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

#let consistent = textsf("consistent")

#let gt = math.upright(math.bold("t"))
#let gs = math.upright(math.bold("s"))
#let fflex = $upright(f)$
#let frigid = $upright(r)$


In this section, we define the constraint language. Following Pottier and Remy [??], our constraint language uses both expression variables and type variables. 

The syntax is given below. For composition we have $ctrue$, the trivially true constraint, and conjunction $C_1 and C_2$. 
The equality constraint $tau_1 = tau_2$ asserts that the types $tau_1$ and $tau_2$ are equivalent. The _sub_ constraint $tau_1 subset.eq tau_2$ asserts that $tau_2$ 'contains' the structure of the type $tau_1$, the definition of 'contains' is somewhat involved (and thus covered later in the section [??]). The existential constraint $exists alpha. C$ that binds the _flexible_ ($fflex$) type variable $alpha$ in $C$. The universal constraint $forall alpha. C$ that binds the _rigid_ ($frigid$) type variable $alpha$ in C. 
The _implication_ constraint $A ==> C$ that assumes the assumptions $A$ hold in $C$. The instance constraint $x <= tau$ (and substitued form $sigma <= tau$) asserts that the scheme of $x$ can be instantiated to the type $tau$. The definition and let constraints $cdef x : sigma cin C$ and $clet x : sigma cin C$ bind the scheme $sigma$ to $x$ in $C$, with the $clet$ constraint additionally asserting that $sigma$ has one or more instances. 

Constraints are considered equivalent modulo alpha-renaming of all binders, of both type and expression variables.

#syntax(
  syntax-rule(name: [Type Variables], $alpha, beta, gamma$),

  syntax-rule(name: [Constraints], $C ::= &ctrue | cfalse | C and C \ 
  | &exists alpha. C | forall alpha. C \ 
  | &tau = tau | tau subset.eq tau | A ==> C \  
  | &cdef x : sigma cin C | x <= tau | sigma <= tau \ 
  | &clet x : sigma cin C 
  $),

  syntax-rule(name: [Types], $tau ::= alpha | overline(tau) tformer | tau approx tau$),
  syntax-rule(name: [Constrained\ Type Schemes], $sigma ::= cforall(overline(alpha : f), C, tau) $), 

  syntax-rule(name: [Assumptions], $A ::= ctrue | A and A | tau = tau$),
  
  syntax-rule(name: [Assignments], $phi ::= dot | phi[alpha -> gt : f]$), 

  syntax-rule(name: [Environments], $rho ::= dot | rho[x |-> gs]$), 

  syntax-rule(name: [Contexts], $Delta ::= dot | Delta, alpha : f | Delta, x$),

  syntax-rule(name: [Flexibility], $f ::= fflex | frigid$),
)

#let rigid = textsf("rigid")

Our constraint language distinguishes between flexible and rigid type variables. Types in assumptions $A$ must be _fully rigid_ -- that is to say no flexible variables may occur. The lower bound $tau_1$ of sub-structural constraints $tau_1 subset.eq tau_2$ must be _rigid_ -- either a rigid variable or a type former. 

#judgement-box($Delta tack tau rigid$)
$
  #proof-tree(
    rule(
      $Delta tack alpha rigid$, 
      $alpha : frigid in Delta$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack overline(tau) tformer rigid$, 
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack tau_1 approx tau_2 rigid$, 
      $Delta tack tau_1 rigid$, 
      $Delta tack tau_2 rigid$
    )
  )
$


Our semantics reflects these restrictions
by tagging assignments with their flexibility. We define 
the restriction $phi_(| f)$ on assignments as removing all variables with flexibility $f'$ not equal to $f$. 
$
  (dot)_(| f) &= dot \ 
  (phi[alpha |-> gt : f'])_(| f) &= cases(
    phi_(| f)[alpha |-> gt : f'] &"if" f = f', 
    phi_(| f) &"otherwise"
  ) 
$

We have an equivalent operation on contexts, denoted $Delta_(| f)$:
$
  (dot)_(| f) &= dot \ 
  (Delta, alpha : f')_(| f) &= cases(
    Delta_(| f)\, alpha : f' &#h1&"if" f = f', 
    Delta_(| f) &&"otherwise"
  ) \ 
  (Delta, x)_(| f) &= Delta_(| f), x
$



#judgement-box($Delta tack.r C ok$)
$
  #v2 
  
  #proof-tree(
    rule(
      $Delta tack.r ctrue ok$, 
      $$,
      name: [(True)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack.r cfalse ok$, 
      $$, 
      name: [(False)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack.r C_1 and C_2 ok$, 
      $Delta tack.r C_1 ok$, 
      $Delta tack.r C_2 ok$, 
      name: [(Conj)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack exists alpha. C ok$, 
      $Delta, alpha : fflex tack.r C ok$, 
      $alpha \# Delta$, 
      name: [(Exists)]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Delta tack forall alpha. C ok$, 
      $Delta, alpha : frigid tack.r C ok$, 
      $alpha \# Delta$, 
      name: [(Forall)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack tau_1 = tau_2 ok$, 
      $forall i. space Delta tack tau_i ok$, 
      name: [(Equal)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack.r tau_1 subset.eq tau_2 ok$, 
      $Delta tack tau_1 rigid$,
      $Delta tack tau_2 ok$, 
      name: [(Sub)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack A ==> C ok$, 
      $Delta_(| frigid) tack A ok$, 
      $Delta tack C ok$, 
      name: [(Impl)]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Delta tack cdef x : sigma cin C ok$, 
      $Delta tack sigma ok$, 
      $Delta, x tack C ok$, 
      $x \# Delta$, 
      name: [(Def)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack x <= tau ok$, 
      $x in dom(Delta)$, 
      $Delta tack tau ok$,
      name: [(VarInst)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack sigma <= tau ok$,
      $Delta tack sigma ok$, 
      $Delta tack tau ok$, 
      name: [(SchemeInst)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack clet x : sigma cin C ok$, 
      $Delta tack sigma ok$, 
      $Delta, x tack C ok$, 
      $x \# Delta$, 
      name: [(Let)]
    )
  ) 

  #v2 

  #proof-tree(
    rule(
      $Delta tack cforall(overline(alpha : f), C, tau) ok$, 
      $Theta tack C ok$, 
      $Theta tack tau ok$,
      $overline(alpha) \# Delta$, 
      label: $Theta = Delta, overline(alpha : f)$, 
      name: [(Scheme)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack ctrue ok$, 
      $$,
      name: [(AssumTrue)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack A_1 and A_2 ok$, 
      $Delta tack A_1 ok$, 
      $Delta tack A_2 ok$, 
      name: [(AssumConj)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack tau_1 = tau_2 ok$, 
      $Delta tack tau_1 ok$, 
      $Delta tack tau_2 ok$, 
      name: [(AssumEqual)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack alpha ok$, 
      $alpha in dom(Delta)$, 
      name: [(TypeVar)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack overline(tau) tformer ok$,
      $forall i. space Delta tack tau_i ok$, 
      name: [(TypeFormer)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack tau_1 approx tau_2 ok$, 
      $Delta tack tau_1 ok$, 
      $Delta tack tau_2 ok$, 
      name: [(TypeApprox)]
    )
  )

$


== Algebra of Types

We now define the the algebra of types, that is their syntax and semantic interpretation. The grammar of types $tau$ is defined as:
$
  tau ::= alpha | overline(tau) tformer | tau approx tau
$

Let $cal(S)$ be a _signature_ for type formers, defining an arity function $arity_cal(S)$ mapping type formers $tformer$ to their arity $n in NN$. A type $tau$ is well-formed in the context of the signature $cal(S)$, written $cal(S) tack tau$, if each occurance of the type former $overline(tau') tformer$ has the correct arity $|overline(tau')| = arity_cal(S)(tformer)$.  

Our algebra is associated with a equational theory $E(equiv)$ defined by the following set of axioms:

$
  tau approx tau &equiv tau \
  tau_1 approx tau_2 &equiv tau_2 approx tau_1 \
  tau_1 approx (tau_2 approx tau_3) &equiv (tau_1 approx tau_2) approx tau_3 \
  (tau_1, ..., tau_2 approx tau_2^', ..., tau_n) tformer &equiv (tau_1, ..., tau_2, ..., tau_n) tformer approx (
    tau_1, ..., tau_2^', ..., tau_n
  ) tformer
$

We consider types equivalent modulo $scripts(equiv)_(\\ "Dist")$ -- that idempotence, associativity, and commutativity. 

#let rnf = textsf("rnf")
#let amb = textsf("amb")

There would be several notions of normal forms for distributivity. We could _expand_ types by applying the left-to-right direction, repeatedly duplicating the head type-formers until we get sets of non-ambivalent types. Instead we propose to _reduce_ types by applying the right-to-left direction as much as possible. This gives a notion of normal forms where, in a type of the form $tau_1 approx dots approx tau_n$, any given type-former occurs at most once as the head of a $tau_i$.

This notion of "reduced" normal form coincides with the behavior we expect from the constraint solver, where the decomposition rules during unification will enforce this form of maximal sharing.

We give a syntax to these reduced normal forms (RNF) below.
The function $rnf$ for converting types to RNFs is straightforward, if relatively tedious. We make use of auxiliary functions $amb(N, N)$ which relies on the ability
to re-order normal forms using commutativity. 

$
  A &::= alpha | overline(N) tformer #h1 N &::= A | N approx A
$

#judgement-box($rnf(tau) : N$) 
$
  rnf(alpha) &= alpha \ 
  rnf(overline(tau) tformer) &= overline(rnf(tau)) tformer \ 
  rnf(tau_1 approx tau_2) &= amb(rnf(tau_1), rnf(tau_2))
$
#judgement-box($amb(N, N) : N$) 
$
  amb(N, alpha) &= cases(
    N &"if" alpha in N, 
    N approx alpha #h1&"otherwise"
  ) \ 

  amb(N_1, overline(N_2) tformer) &= cases(
    N'_1 approx overline(amb(N'_2, N_2)) tformer #h1&"if" N_1 = N'_1 approx overline(N'_2) tformer,
    overline(amb(N'_2, N_2)) tformer &"if" N_1 = overline(N'_2) tformer,
    N_1 approx overline(N_2) tformer &"otherwise"
  ) \ 


  amb(N_1, N_2 approx A) &= amb(N_1, amb(N_2, A))
$

Having defined RNF, we may now define what it means for a type $tau_2$ to _contain_ a type $tau_1$, written $tau_1 subset.eq tau_2$. 
$
  #proof-tree(
    rule(
      $tau_1 subset.eq tau_3$, 
      $rnf(tau_1) approx tau_2 = rnf(tau_3)$,
    )
  )
$

To motative the removal of implicit distributivity. 
Consider the constraint
$
  alpha tlist subset.eq tint tlist approx tstring tlist.
$
Without the restrictions on distributivity, there are 3 possible assignments for $alpha$ that would satisfy the above constraint:
$
  alpha &|-> tint \ 
  alpha &|-> tstring \ 
  alpha &|-> tint approx tstring 
$

The first two assignments result in a loss of ambivalence for $alpha$ -- this is something our constraints _should not_ capture. By requiring the RHS to be in RNF, we remove the distributive occurance of $tlist$, enforcing the third assignment of $alpha$. 


*Semantics*. We now formally define the semantic interpretation of types. Informally, the model consists of a tree of type constructors or ambivalent types. 
$
  gt ::= overline(gt) tformer | gt approx gt
$

The interpretation of a type $tau$, under the ground assignment $phi$, written $phi(tau)$ is defined by:
$
  phi(alpha) &= gt &"where" phi(alpha) = gt : f \ 
  phi(overline(tau) tformer) &= overline(phi(tau_i)) tformer \
  phi(tau_1 approx tau_2) &= phi(tau_1) approx phi(tau_2)
$

The $f$-flexible interpretation of the type $tau$ under the ground assignment $phi$, written $phi^f (tau)$, is defined by:
$
  phi^f (alpha) &= cases(
    gt &"if" phi(alpha) = gt : f' and f = f',  
    "undefined" #h1 &"otherwise"
  ) \ 
  phi^f (overline(tau) tformer) &= overline(phi^f (tau_i)) tformer \
  phi^f (tau_1 approx tau_2) &= phi^f (tau_1) approx phi^f (tau_2)
$

A ground type $gt$ is consistent, written $consistent(gt)$, iff it doesn't contain $approx$. The name comes from the fact that if a ground type is in reduced normal form and still contains type subpexression of the form $gt_1 approx gt_2$, then $gt_1$ and $gt_2$ are necessarily incompatible ground types.


== Semantics

Our constraints are interpreted under the model of ground types. A ground (or semantic) assignment $phi$ is a partial function from type variables $alpha$ to ground types $gt$ (and flexibilities). 

Implication constraints introduce equalities. These are taken into account using a _consistency bit_ $kappa$. If we are in a consistent context, then it follows that only reflexive equalities $gt = gt$ have been introduced. Otherwise we are in an inconsistent context. Consistency affects the types we can introduce in existential binders $exists alpha. C$ -- namely if we are in a consistent context, then it follows that the type assigned to $alpha$ must be consistent. 

An _environment_ $rho$ is a partial function from expression variables $x$ to _ground type schemes_ $gs$ -- a set of consistency and ground type pairs $kappa tack gt$, known as a _ground instance_, which reflects that the scheme was instantiated to $gt$ under the consistency $kappa$. 


The satisfiability judgement for constraints $kappa; phi; rho tack C$ states that _in the environment $rho$ with consistency $kappa$, the assignment $phi$ satisfies the constraint $C$_. 


#judgement-box($kappa, phi, rho tack.r C $)
$
  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack.r ctrue$, 
      "",
      name: [(True)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack.r C_1 and C_2$,
      $kappa, phi, rho tack.r C_1$,
      $kappa, phi, rho tack.r C_2$,
      name: [(Conj)]
    )
  )


  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack.r exists alpha. C$, 
      $kappa => consistent(gt)$, 
      $kappa, phi[alpha |-> gt], rho tack.r C$,
      name: [(Exists)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack.r forall alpha. C$, 
      $forall gt$, 
      $kappa and consistent(gt), phi[alpha |-> gt], rho tack.r C$, 
      name: [(Forall)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack.r tau_1 = tau_2$,
      $phi(tau_1) = phi(tau_2)$, 
      name: [(Equal)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack.r tau_1 subset.eq tau_2$,
      $phi^frigid (tau_1) subset.eq phi(tau_2)$, 
      name: [(Sub)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack.r A ==> C$, 
      $kappa and phi_(| frigid)(A), phi, rho tack.r C$, 
      name: [(Impl)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack cdef x : sigma cin C$, 
      $kappa, phi, rho[x |-> (phi, rho) sigma] tack C$, 
      name: [(Def)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack x <= alpha$, 
      $kappa tack phi(alpha) in rho(x)$, 
      name: [(VarInst)]
    )
  )


  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack sigma <= alpha$, 
      $kappa tack phi(alpha) in (phi, rho) sigma$, 
      name: [(SchemeInst)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack clet x : sigma cin C$, 
      $kappa, phi, rho tack exists sigma$, 
      $kappa, phi, rho[x |-> (phi, rho) sigma] tack C$, 
      name: [(Let)]
    )
  ) 

  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack exists (cforall(overline(alpha : f), C, tau))$, 
      $kappa, phi, rho tack forall overline(alpha). exists overline(beta). C$, 
      name: [(SchemeSat)]
    )
  )
$

The interpretation of the constrained type scheme $cforall(overline(alpha : f), C, tau)$ in the assignment $phi$ contains all ground instances $kappa' tack (phi,phi')(tau)$ which satisfy $C$, where $phi$ is extended with a disjoint assignment $phi'$ for the $overline(alpha)$, that has to pick only consistent ground variables when $kappa'$ is consistent:
$
  (phi, rho)(cforall(overline(alpha : f), C, tau)) = { kappa' tack (phi,phi')(tau) :
    &dom(phi') = overline(alpha)
    and kappa' => consistent(phi') \
    &and kappa', (phi, phi'), rho tack C }
$

#comment[Note: It is odd that the interpretation of schemes doesn't include the consistency at which is was defined. The reasoning behind this that consistency can only decrease and that satisfiability is stable under consistent (i.e. a constraint satisfiable under true is satisfiable under false). Since consistency is referenced in the instance, this ensures that under a 'true' context, the scheme must be satisfable under a true assignment. The let constraint ensures that the scheme must have some instances under the current satisfiability using the $exists sigma$ judgement. This allows us to have the standard let = def + satisfiability check equivalence.]

A constraint $C_1$ entails $C_2$, written $C_1 tack.double C_2$, if every context that satisfies $C_1$ also satisfies $C_2$. Similarly, equivalence $C_1 equiv C_2$ holds if the property is bidirectional.

In our semantics, the $cdef$ form is an _explicit substitution_. More formally, the semantics satisfy the equivalence law:
$
  cdef x : sigma cin C equiv C[x := sigma]
$
Instantiation constraints satisfy the equivalence law:
$
  (forall overline(alpha), overline(beta). C => tau) <= delta equiv exists overline(alpha), overline(beta). C and gamma = delta
$
$clet$ forms are equivalent to $cdef$ constraints that check the satisfiability of the constrainted type scheme:
$
  clet x : underbrace(cforall(overline(alpha : f), C_1, tau), sigma)  cin C_2 equiv (forall overline(alpha). exists overline(beta). C_1) and cdef x : sigma cin C_2 
$


#pagebreak()

== Constraint Generation

We introduce a function $[| e : alpha |]$, which translates the expression $e$ and type variable $alpha$ to a constraint. Assuming $e$ is well-formed under $Delta$ ($Delta tack e ok $), then $[| e : alpha |]$ is well-formed under $Delta$ and $alpha$ ($alpha : fflex, Delta tack [|e : alpha|] ok$). 


$
  
  [| x : alpha |] &= x <= alpha \ 
  [| efun x -> e : alpha |] &= exists alpha_1 alpha_2. cdef x: alpha_1 cin [| e : alpha_2 |] and alpha supset.eq alpha_1 -> alpha_2 \ 
  [| e_1 space e_2 : alpha |] &= exists alpha_1, alpha_2. [| e_1 : alpha_1 |] and [| e_2 : alpha_2 |] and alpha_1 supset.eq alpha_2 -> alpha  \ 
  [| clet x = e_1 cin e_2 : alpha |] &= clet x : paren.l.double e_1 paren.r.double cin [| e_2 : alpha |] \ 
  [| efun (etype beta) -> e : alpha |] &= clet x : paren.l.double e paren.r.double_beta cin x <= alpha \ 
  [| (e : tau) : alpha |] &= alpha supset.eq tau and [| e : tau |] \ 
  [| erefl : alpha |] &= exists alpha_1. alpha supset.eq (alpha_1 = alpha_1) \ 
  [| ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : alpha |] &= [| e_1 : tau_1 = tau_2 |] and (tau_1 = tau_2) ==> [| e_2 : alpha |]
$

$
  paren.l.double e paren.r.double &= forall alpha. [| e : alpha |] => alpha \ 
  paren.l.double e paren.r.double_alpha &= forall alpha, beta. [| e : beta |] => beta 

$

We can additional extend the constraint generation function $[| e : alpha |]$ to be defined on $[| e : tau |]$
$
  [| e : tau |] &= exists alpha. alpha  tau and [| e : alpha |]
$


// == Problems 


// Substitutivity of rigid types

// ```ocaml
// let coerce = 
//   fun (type a b) -> fun w -> fun x -> 
//   let w = (w: (a, b) eq) in 
//   let x = (x: a) in
//   match (w : (a, b) eq) with Refl -> (x : b)

// let f =
//   fun (type a) -> fun w -> fun x -> 
//   let w = (w : (a, int) eq) in 
//   let x = (x : a) in 
//   match (w : (a, int) eq) with Refl -> 
//       let y = if true then x else 1 in 
//       ignore (coerce Refl y) 
// ```

// Generated constraints:

// $
//   paren.double.l"coerce"paren.double.r_(alpha, beta) &= forall alpha, beta, zeta. \ 
//     & exists zeta_w, zeta_x, zeta_r. zeta_w -> zeta_x -> zeta_r cis zeta and   cdef w: zeta_w, x: zeta_x cin \ 
//     &clet w: forall zeta_w'. alpha = beta cis zeta_w' and w <= alpha = beta => zeta_w' cin \ 
//     &clet x: forall zeta_x'. alpha cis zeta_x' and x <= alpha cin \ 
//     &[| w : alpha = beta|] and alpha = beta ==> exists zeta_r'. beta cin zeta_r and beta cin zeta_r' and x <= zeta_r' \

//     &=> zeta
// $

// Doing some solving, we get
// $
//  paren.double.l"coerce"paren.double.r_(alpha, beta) &= forall alpha, beta, zeta_w, zeta_x, zeta_r, zeta. \
//  &#h1 zeta_w -> zeta_x -> zeta_r cis zeta \ 
//  &#h1 and alpha = beta cin zeta_w and alpha cin zeta_x and beta cin zeta_r  => zeta
// $

// Ah ha! So this split means we don't propagate ambivalence correctly! Since if apply a value with $zeta = zeta$ for `w` where $zeta$ is ambivalent $alpha approx "int"$, then the return annotation $beta cin zeta_r$ doesn't ensure that the ambivalence is propagated. Something is wrong with our spec!

// Now Olivier's rule for applying `coerce` does trace ambivalence, but it breaks substitution on implication constraints. 



// Now looking at `f`:
// $
//   [| f : zeta |] &= 
//     clet f_1 : forall alpha, zeta_1 . [| ... : zeta_1 |] => zeta_1 
//     cin f_1 <= zeta \ 

//   [| ... : zeta_1 |] &= exists zeta_w, zeta_x, zeta_r. 
//   zeta_w -> zeta_x -> zeta_r cis zeta_1 \ 
//   &and
//   cdef w : zeta_w, x : zeta_x cin [| ... : zeta_r |] \ 

//   [| ... : zeta_r|] &= clet w : forall zeta_w'. alpha = "int" cis zeta_w' and w <= alpha = "int" => zeta_w', \
//   &#h1 x : forall zeta_x'. alpha cis zeta_x' => zeta_x' and x <= alpha => zeta_x' \
//   &#h1 cin [| ... : zeta_r|]\
//   [| ematch ... : zeta_r|] &= [| w : alpha = "int" |] and alpha = "int" ==> [| ... : zeta_r |] \ 
//   [| clet y = ... : zeta_r|] &= clet y : forall zeta_y. x <= zeta_y and "int" cis zeta_y => zeta_y cin [| ... : zeta_r |] \ 
//   [| "ignore" ... : zeta_r |] &= "unit" cis zeta_r and exists zeta'. [| "coerce" erefl y : zeta' |] 
// $



// == Metatheory

// - Theorem: $ctrue, emptyset, emptyset tack C ==> dot tack C ok$

// - Soundness: Assume $Theta; Delta tack e ok $, $dom(phi) = Theta$ and $Delta tack Gamma ok$. Then,  \ $Theta; Xi; phi(Gamma) tack phi(e) : phi(chi) ==> phi(Xi), phi, phi(Gamma) tack [| e : chi |]$

// We proceed by rule induction on $Delta; Theta; Gamma tack e : chi$ with the statement:

// $
// P(Theta; Xi; Gamma tack e : chi) := forall phi. dom(phi) = Theta and phi (Theta; Xi; Gamma tack e : chi) ==> phi(Xi), phi, phi(Gamma) tack [| e : chi |] 
// $


// Case (Var)

// 1. Assume $phi (Theta; Xi; Gamma tack e : chi)$ 
// 2. By inversion of (Var): 
//    $
//      #proof-tree(
//        rule(
//          $Theta; Xi; Gamma tack e : chi_1[overline(alpha := tau), overline(zeta := chi_2)]$, 
//          $Gamma(x) = forall overline(alpha), overline(zeta). chi_1$, 
//          $Theta tack tau_i ok $, 
//          $Theta; Xi tack chi_(2j) ok $
//        )
//      )
//    $
//    We have 
//    $
//      phi(chi) &= chi_1[overline(alpha := tau), overline(zeta := chi_(2j))] \ 
//      phi(Gamma(x)) &= forall overline(alpha), overline(zeta). chi_1 \
//      dot tack tau_1 ok \ 
//      dot; phi(Xi) tack chi_(2j) ok
//    $ 
// 3. We wish to show that $phi(Xi), phi, phi(Gamma) tack [| x : chi |]$, that is:
// $
//   [| x : chi|] &= exists zeta. chi subset.eq zeta and [| x : zeta |] \ 
//   &= exists zeta. chi subset.eq zeta and x <= zeta 
// $
// 4. Define $phi' = phi[zeta |-> phi(chi)]$. We have $phi(Xi), phi', phi(Gamma) tack chi subset.eq zeta$
// 5. 
// $
//   phi(Xi), phi', phi(Gamma) tack x <= zeta \ 
//   <==> phi'(zeta) in phi(Gamma)(x) \ 
//   <==> phi(chi) in (dot; phi; emptyset)(forall overline(alpha), overline(zeta). chi_1) \ 
//   <==> exists phi''. phi(chi) = phi'' (chi_1) and phi scripts(=)_(\\ overline(alpha), overline(zeta)) phi''
// $
// 6. Define $phi'' = phi[overline(alpha := tau), overline(zeta := chi_2)]$. We have $phi scripts(=)_(\\ overline(alpha), overline(zeta)) phi''$ and $phi''(chi_1) = chi_1[overline(alpha := tau), overline(zeta := chi_2)] = phi(chi)$


// Case (Fun)

// 1. Assume $phi (Delta; Xi; Gamma tack efun x -> e' : chi)$
// 2. By inversion of (Fun) 
//    $
//      #proof-tree(
//       rule(
//         $Theta; Xi; Gamma tack efun x -> e' : chi_1 -> chi_2$, 
//         $Theta; Xi; Gamma, x: chi_1 tack e' : chi_2$
//       )
//      )
//    $
//    We have 
//    $
//       phi(chi) &= chi_1 -> chi_2 \
//       P(Theta; Xi; Gamma, x : chi_1 tack e' : chi_2)
//    $
// 3. Define $phi' = phi[zeta |-> phi(chi), zeta_1 |-> chi_1, zeta_2 |-> chi_2]$
// 4. ... $
//      [| efun x -> e' : zeta |] &= exists zeta_1, zeta_2. zeta_1 -> zeta_2 subset.eq zeta and cdef x : zeta_1 cin [| e' : zeta_2 |]
//    $


// #pagebreak()


// - & completeness: $Gamma tack e : chi <==> kappa(Gamma), phi, phi(Gamma) tack [| e : chi|]$ assuming $Gamma tack e ok$ 

// $
// kappa(Gamma) = cases(
//   cfalse &#h(1cm)&"if" Gamma textsf("incon") \
//   ctrue &&"otherwise"
// )
// $

// $
  
//   #proof-tree(
//     rule(
//       $Gamma textsf("incon")$, 
//       $Gamma tack overline(chi)_1 tformer eq.triple overline(chi)_2 textsf("G")$, 
//       $tformer != textsf("G")$
//     )
//   )
// $


// 
// fun (x : tau) -> e = fun x -> let x = (x : tau) in e