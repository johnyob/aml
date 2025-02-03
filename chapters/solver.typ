#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *


We define the constraint solver as a stack machine. Our machine is defined in terms of a transition relation on states of the form $(S, U, C)$, consisting of a stack $S$, a unification problem $U$, and an in-progress constraint $C$. 

#let sscope = $phi.alt$

_Stacks_. The stack $S$ represents the context in which $U and C$ appears. It contains the bindings for flexible and rigid type variables, term variables, and _assumptions_, that may appear in $U and C$. 
Our states are closed, meaning $S$ must bind all free variables in $U and C$. 

#syntax(
  syntax-rule(
    name: [Frames], 
    $F ::= &square and C |  exists alpha. square | forall a. square \ 
    | &cdef x : sigma cin square \
    | &clet x : cforall(#($overline(alpha), overline(a)$), square, tau)  cin C \
    | &clet x : hat(sigma) cin square \
    | &phi.alt : A  ==> square
    $
  ), 


  syntax-rule(
    name: [Stacks], 
    $S ::= dot | S :: F$
  ),
)
#let tformera = $op(tformer)^a$
#let sptformera = $space tformera$

// Holes
The stack additionally indicates how to continue after $C$ has been solved. The different forms of stack frames directly correspond to those constraints with at least one subconstraint. The overall stack can then be seen as a constraint with a hole in which $C$ is plugged.


// Rigid variables + Skolem constructors 
Unlike Pottier and Rémy's presentation for universal quantification in [??], our solver differentiates flexible and rigid type variables, with rigid ones encoded as a _Skolem constructors_ [??]. We write $tformera$ for either a type constructor $tformer$ or a Skolem constructor $a$. 
Additionally we treat Skolem constructors as nullary type constructors.

// Explaination on assumption names
In implication frames $sscope : A ==> square$, we annotate the assumptions $A$ with a name $sscope$ to be able to refer to it during unification and when checking whether an introduced assumption escapes its _scope_. This not only improves the formalisation but better matches our implementation which uses integers to represent scopes [??]. 

_Unification Problems_.  Our constraints are eventually reduced to equations on first-order terms (solved under a mixed prefix). We express these reduced constraints as _unification problems_ $U$, which form a subset of constraints. We define _unification_ as a (non-deterministic) transition relation on _unification problems_. 


#let umultieq = $epsilon.alt$
#let umultilb = $eta$
#let umulti(phi, lb, eq) = $#phi tack #lb subset.eq #eq$
$
  U &::= ctrue | cfalse | U and U | exists alpha. U | umulti(Phi, umultilb, umultieq) \
  umultieq &::= dot | umultieq = tau \ 
  eta &::= dot | eta union.sq tau \
  tau &::= alpha | overline(tau) tformera | tau approx tau\
  tformera &::= tformer | a  
$

// Multi-equations 
Following Pottier and Remy, we replace ordinary binary atomic constraints such as equality $tau_1 = tau_2$ and containment $tau_1 subset.eq tau_2$ with a _mutli-relation_. A _multi-relation_ $Phi tack umultilb subset.eq umultieq$ is a 
an equality between an arbitrary number of types $umultieq$ with an arbitrary number of containment relations $eta$ that are associated with a single upper-bound that relies on the assumptions $Phi$. The interpretation of a multi-equation is given by 
$
  #proof-tree(
    rule(
      $kappa, phi, rho tack umulti(Phi, umultilb, umultieq)$, 
      $exists gt$, 
      $consistent(gt) ==> and.big phi(Phi)$, 
      $forall tau in umultieq. space phi(tau) = gt$, 
      $forall tau^frigid in eta. space phi^frigid (tau^frigid) subset.eq gt$
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack sscope : A ==> C$, 
      $kappa and kappa', phi[sscope |-> kappa'], rho tack C$, 
      $kappa' = phi(A)$
    )
  )
$
That is, $phi$ satisfies $umulti(Phi, umultilb, umultieq)$ if all members of $umultieq$ are mapped to a single ground type by $phi$ which contains all types in $umultilb$. 
Note that the above rule extends assignments $phi$ to interpret the consistency of named assumptions $sscope$. 

$
  #proof-tree(
    rule(
      $Delta tack sscope : A ==> C ok$, 
      $Delta, sscope tack C ok$, 
      $Delta_(| frigid) tack A ok$, 
      $sscope in.not Delta$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack umulti(Phi, umultilb, umultieq) ok$,
      $Phi subset.eq Delta$, 
      $forall tau^frigid in umultilb. space Delta tack tau^frigid rigid$, 
      $forall tau in umultieq. space Delta tack tau ok$
    )
  )
$


// Solver contexts and well-formedness
#let srv = textsf("rv")
#let sfv = textsf("fv")
#let sass = textsf("assm")
#let stmv = textsf("tmv")
#let styv = textsf("tyv")
#let sc = textsf("c")

We write $srv(S)$, $sfv(S)$, and $sass(S)$ for the rigid variables, flexible variables and _named assumptions_ in the stack $S$, respectively. 
We write $stmv(S)$ and $styv(S)$ for the term and type variables (flexible or rigid) bound in $S$, the latter is defined as $srv(S), sfv(S)$. 
We write $(stmv(S), styv(S), sass(S))$ for the context synthesized from $S$, denoted $sc(S)$. 

$
  srv(S) &= cases(
    dot &"if" S = dot, 
    srv(S')\, a &"if" S = S' :: forall a. square,
    srv(S')\, overline(a) &"if" S = S' :: clet x : forall overline(alpha)\, overline(a). square => tau cin C, 
    srv(S') #h1&"otherwise" (S = S' :: \_)
  )
  
  #v2

  sfv(S) &= cases(
    dot &"if" S = dot, 
    sfv(S')\, alpha &"if" S = S' :: exists alpha. square,
    sfv(S')\, overline(alpha) &"if" S = S' :: clet x : forall overline(alpha)\, overline(a). square => tau cin C, 
    sfv(S') #h1&"otherwise" (S = S' :: \_)
  ) 

  #v2 

  sass(S) &= cases(
    dot &"if" S = dot, 
    sass(S')\, sscope: A #h(.5cm) &"if" S = S' :: sscope : A ==> square, 
    sass(S') &"otherwise" (S = S' :: \_)
  )

  #v2

  stmv(S) &= cases(
    dot &"if" S = dot, 
    stmv(S')\, x #h1&"if" S = S' :: cdef x : sigma cin square, 
    &"or" S = S' :: clet x : hat(sigma) cin square, 
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
      $alpha in.not styv(S)$, 
    )
  )

  #h1 

  #proof-tree(
    rule(
      $tack S :: forall a. square ok$, 
      $tack S ok$, 
      $a in.not styv(S)$
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
      $tack S :: clet x : cforall(#($overline(alpha), overline(a)$), square, tau) cin C ok$, 
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
      $tack S :: sscope : A ==> square ok$, 
      $tack S ok$, 
      $sscope in.not sass(S)$, 
      $srv(S) tack A ok$, 
    )
  )
$

To check the well-formedness of constraints embedded in stack frames, the rules $tack S ok$ use the contexts induced by $S$. 
These judgements only ensure the term variables, type variables and named assumptions used in constraints are bound in $S$. 
In order for the state $(S, U, C)$ to be well-formed ($tack (S, U, C) ok$), we require that $S$ is well-formed ($tack S ok$), $U$ and $C$ are well-formed in $sc(S)$. 

// Ordering on assumptions

#let sminass = textsf("min-assm")


== Solver Rules 

We now introduce the rules of the constraint solver itself. 
The solver consists of a (non-deterministic) state rewriting system, given in Figure ??. We assume re-writings are performed modulo 
$alpha$-renaming and commutativity of conjunctions and multi-relational structures. 

A constraint is satisfiable in a given context if the solver reaches a state of the form ($cal(X), hat(U), ctrue$) where $cal(X)$ is an existential stack context and $hat(U)$ is a _satisfiable solved form_ of a unification problem from an initial configuration build from $C$ $(square, ctrue, C)$. From such a final state, we can read off a most general solution for the constraint by interpreting $hat(U)$ as a substitution. If the constraint is unsatisfiable, the solver reaches a state of the form $(S, cfalse, C)$. 


#let occurs = $textsf("occurs in")$

_Unification_. 
The relation $U -->_S U'$ describes the unification algorithm in the _context_ $S$. We often omit $S$ when it is unncessary. 
We say $alpha occurs beta$ with respect to $U$ if $U$
contains a multi-relation of the form $tau diamond.small alpha diamond.small' ...$ 
where $tau$ is a non-variable type satisfying $beta in fv(tau)$ and $diamond.small$ denotes some relation (either $=$ or $subset.eq$). 
A unification problem $U$ is cyclic if there exists $alpha$ such that $alpha occurs alpha$ wrt. $U$. 

A _solved form_ $hat(U)$ is either $cfalse$ or $exists overline(alpha). and.big_i epsilon.alt_i$ where 
every multi-equation contains at most one non-variable type (either in a equality or lower-bound position), no two multi-equations share a variable, $hat(U)$ is not cyclic.  Similarly, a _solved scheme_ $hat(sigma)$ is a constrainted type scheme of the form $cforall(#($overline(alpha), overline(a)$), hat(U), beta)$. 


#let tformerga = $space textsf("G")^a$
$
  // Common rules
  (exists alpha. U_1) and U_2 &--> exists alpha. U_1 and U_2 &#h(2cm)&"if" alpha \# U_2 \ 

  U &--> cfalse 
  &&"if" U "is cyclic" \ 

  cal(U)[cfalse] &--> cfalse \

  cal(U)[U] &--> cal(U)[U']  
  &&"if" U --> U' \ 

  U and ctrue &--> U \ 

  U_1 and U_2 &--> U_2 and U_1 \

  // Merge rules
  Phi tack alpha = alpha = epsilon.alt supset.sq.eq eta &--> Phi tack alpha = epsilon.alt supset.sq.eq eta \ 


  Phi tack alpha = epsilon.alt supset.sq.eq eta and Phi' tack alpha = epsilon.alt' supset.sq.eq eta' &--> Phi union Phi' tack alpha = epsilon.alt = epsilon.alt' supset.sq.eq eta union.sq eta' \ 

  // Decomposition rules 
  // Phi tack cal(X)[(tau_1, ..., tau_i, ..., tau_n) tformer] &--> exists alpha. alpha = tau_i and Phi tack cal(X)[(tau_1, ..., alpha, ..., tau_n) tformer] \


  // Former-Former 
  Phi tack umultieq supset.sq.eq psi_1[overline(alpha_1) tformera] union.sq psi_2[overline(alpha_2) tformera] union.sq eta &--> Phi tack umultieq supset.sq.eq (psi_1 approx psi_2) union.sq eta and and.big_i alpha_(1i) = alpha_(2i) \

  // Former-Former Not Equal 
  Phi tack umultieq supset.sq.eq psi_1[overline(alpha_1) tformera] union.sq psi_2[overline(alpha_2) tformerga] union.sq eta &-->_S Phi union Phi' tack umultieq supset.sq.eq (psi_1 approx psi_2) union.sq eta and and.big alpha_(1i) supset.sq.eq tau_(1i) \ 
  &#h1 and and.big_j alpha_(2i) supset.sq.eq tau_(2i)  \

  &#h1 "if" tformera eq.not tformerga and Phi' in sminass(S, Phi, overline(tau_1) tformera = overline(tau_2) tformerga) \

  // Clash
  overline(sscope) tack umultieq supset.sq.eq psi[rho_1] union.sq psi'[rho_2] union.sq eta &-->_S cfalse 
  \ 
  &#h1 "if" (and.big sass(S) ==> exists alpha. rho_1 subset.eq alpha and rho_2 subset.eq alpha )equiv cfalse 
$

// Description of the algorithm
The unification algorithm is largely standard with the exception of the treatment of _mutli-relations_. Multi-relations are adapted from multi-equations [??]
but are extended to handle ambivalence. Note that the unification algorithm treats rigid variables as Skolem constructors. The algorithm preserves semantic equivalence and terminates. 

#comment[TODO -- add something on scopes]

_Atomic constraints_. 


_Quantifiers_. 


_Let binders_.  


_Implications_. 


$
 (S, U, alpha = beta) &--> (S, U and tack alpha = beta, ctrue) \ 

 (S, U, psi subset.eq alpha) &--> (S, U and tack psi subset.eq alpha, ctrue) \

 (S, U, C_1 and C_2) &--> (S :: square and C_2, U, C_1) \ 

 (S, U, exists alpha. C) &--> (S :: exists alpha. square, U, C) &#h(2cm)&"if" alpha \# U \ 


 (S, U, cdef x : sigma cin C) &--> (S :: cdef x : sigma cin square, U, C) \ 

 (S, U, x <= tau) &--> (S, U, S(x) <= tau) \ 

 (S, U, clet x : cforall(overline(alpha : f), C_1, tau) cin C_2) &--> (S :: clet x : cforall(#($overline(beta), overline(a)$),  square, tau) cin C_2, U, C_1[overline(gamma := a)]) &&"if" overline(alpha : f) = overline(beta : fflex), overline(gamma : frigid)
  
$



== Metatheory 



// Decomposition rules are:
// $
//  (S, U, tau_1 = tau_2) &--> (S, U and tau_1 = tau_2, ctrue) \ 

//  (S, U, C_1 and C_2) &--> (S :: square and C_2, U, C_1) \ 

//  (S, U, exists alpha. C) &--> (S :: exists alpha. square, U, C) &#h(2cm)&"if" alpha \# U \ 

//  (S, U, cmatch alpha cwith [Gamma] f) &--> (S, U and cmatch alpha cwith [Gamma]f, ctrue) \ 

//  (S, U, cdef x : sigma cin C) &--> (S :: cdef x : sigma cin square, U, C) \ 

//  (S, U, x <= tau) &--> (S, U, S(x) <= tau) \ 

//   // Copy the constraint


//   // Regions:
//   //  Previously linear, but 
//   //  we need to keep gamma alive (non-generalised) s.t 
//   //  if beta is solved, then we unify the gamma and the instantiated gamma
//   //  
//   //  alpha. U and <beta ~> alpha>SU, ret type (variable)
//   // 
//   // forall overline(alpha). C <SU> => alpha 
//   // SU ::= beta ~> alpha | and.big cmatch beta cwith [Gamma]f
//   // 
//   // Linear approach:
//   //   add existentials for alpha that are partially generalised
//   //   SU is solved outside the let constraint
//   //   On instantiation (match beta cwith [alpha'](fun _ -> alpha = alpha'))
//   // 
//   // Doesn't work! Since if alpha is truly general after beta is determined, this fails (womp)
//   // 

//  (S, U, (forall overline(alpha), overline(beta arrow.r.squiggly gamma). C => tau) <= tau') &-->  (S, U, exists overline(alpha), overline(gamma). C and tau = tau' )
// $

// #let append = "++"

// Existential extraction rules are:
// $
//   (S, exists alpha. U, C) &--> (S :: exists alpha. square, U, C) &#h(2cm)&"if" alpha \#C \ 

//   (S :: square and C_1 :: exists alpha. square append S', U, C_2) &--> (S :: exists alpha. square :: square and C_1 append S', U, C_2) &&"if" alpha \# C_1 \

//   (S :: cdef x : sigma cin square :: exists alpha. square append S', U, C) &--> (S :: exists alpha. square :: cdef x : sigma cin square append S', U, C) &&"if" alpha \# sigma
// $

// Solving rules are:
// $
//   (S, U, C) &--> (S, U', C) &#h(2cm)&"if" U --> U' \ 

//   (S, U and alpha = tau = epsilon.alt and cmatch alpha cwith [Gamma]f, ctrue) &--> (S, U and alpha = tau = epsilon.alt, f(tau)) &&"if" tau in.not varty\


//   (dot, exists alpha. cal(U)[cmatch alpha cwith [Gamma]f], ctrue) &--> (dot, cfalse, ctrue) &&"if not" cal(U)[ctrue] determines alpha
// $

// Pop rules:
// $
  
//   (S :: square and C, U, ctrue) &--> (S, U, C) \ 

//   (S :: exists alpha. square, U, ctrue) &--> (S, exists alpha. U, ctrue) &#h(1cm)&"if" alpha in fv(U) \ 

//   (S :: exists alpha. square, U, ctrue) &--> (S, U, ctrue) &&"if" alpha \# U \ 

//   (S :: cdef x : sigma cin square, U, ctrue) &--> (S, clo(S, U), ctrue )
  
// $

#comment[NOTE: These are rough notes and not complete]

#let sscope = $phi.alt$
#let shole = $[dot]$

States extended to add equations:
$
  S ::= ... | S[sscope : A ==> shole]
$

#let seq = textsf("Eqs")

Define function $seq(S): overline(sscope : A)$ that returns list of scoped assumptions for a given state
$
  seq(shole) &= emptyset \
  seq(S[shole and C]) &= seq(S) \
  seq(S[exists alpha. shole]) &= seq(S) \
  seq(S[forall alpha. shole]) &= seq(S) \
  seq(S[clet x : forall overline(alpha), overline(beta). shole cin C]) &= seq(S) \
  seq(S[clet x : hat(sigma) cin shole]) &= seq(S) \
  seq(S[sscope : A ==> shole]) &= seq(S), sscope: A
$

$seq$ defines an order on scoped assumptions.
For $sscope_i, sscope_j in dom(seq(S)) = sscope_1, ..., sscope_n$, we say $sscope_i < sscope_j <==> i > j$.

Unification problems:
#let umultieq = $epsilon.alt$
$
  U &::= ctrue | cfalse | U and U | exists alpha. U | overline(sscope) tack umultieq \
  umultieq &::= dot | umultieq = psi | umultieq = alpha \
  rho &::= overline(alpha) space tformer^a \ 
  tformer^a &::= a | tformer \ 
  psi &::= rho | psi approx rho 
$

// Ambivalent types are notationally odd -- this a convenience in order to inspect the 'head' an an ambivalent type. The head of an ambivalent type must be rigid -- either a rigid variable or type former. We can interpret $rho^(overline(alpha))$ as the ambivalent type $rho approx alpha_1 approx ... approx alpha_n$.


Multi equations are scoped ($overline(sscope)$).

#let srv = textsf("rv")
#let rigid = textsf("rigid")
A shallow type is rigid if it is either a type constructor, ambivalent type or _rigid_ variable (not flexible)

#let smineq = textsf("minEqs")
#let head = textsf("head")

Standard unification rules:
$
  // Standard rules
  (exists alpha. U_1) and U_2 &--> exists alpha. U_1 and U_2 &#h1&alpha in.not fv(U_2)  \
  overline(sscope_1) tack alpha = umultieq_1 and overline(sscope_2) tack alpha = umultieq_2 &--> overline(sscope_1) union overline(sscope_2) tack alpha = umultieq_1 = umultieq_2 \
  overline(sscope) tack alpha = alpha = umultieq &--> overline(sscope) tack alpha = umultieq \
  U &--> cfalse &&U "is cyclic" \
  cal(U)[cfalse] &--> cfalse
$
Decomposition rules. These differ from Olivier's rules since I want to handle ambivalent structures (instead of making them implicit in the multi-equation)

#let tformerg = textsf("G")

$
  // Rigid-Rigid
  // overline(sscope) tack alpha^overline(gamma) = beta^overline(delta) = umultieq &-->_S overline(sscope) union overline(sscope)' tack alpha^(overline(gamma),beta,overline(delta)) = umultieq 
  // &&"if" alpha, beta in srv(S) and overline(sscope)' in smineq(S, overline(sscope), alpha = beta) \ 

  // // Former-Rigid
  // overline(sscope) tack (overline(alpha) tformer)^(overline(gamma)) = beta^overline(delta) = umultieq &-->_S  overline(sscope) union overline(sscope)' tack (overline(alpha) tformer)^(overline(gamma), beta, overline(delta)) = umultieq and and.big_i alpha_i = tau_i && "if" beta in srv(S) and overline(sscope)' in smineq(S, overline(sscope), beta = overline(tau) tformer) \ 

  // Former-Former 
  overline(sscope) tack psi[overline(alpha_1) tformer^a] = psi'[overline(alpha_2) tformer^a] = umultieq &--> overline(sscope) tack psi approx psi' = umultieq and and.big_i dot tack alpha_(1i) = alpha_(2i) \
  \

  overline(sscope) tack psi[overline(alpha_1) tformer^a] = psi'[overline(alpha_2) tformerg^a]^(overline(gamma)) = umultieq &--> overline(sscope), overline(sscope)' tack psi approx psi' = umultieq \
  &#h1 and and.big_i alpha_(1i) = tau_(1i) and and.big_j alpha_(2j) = tau_(2j) 
  &&"if" tformer^a eq.not tformerg^a and overline(sscope)' in smineq(S, overline(sscope), overline(tau_1) tformer^a = overline(tau_2) space textsf("G")^a) \

  // Clash
  overline(sscope) tack psi[rho_1] = psi'[rho_2] = umultieq &-->_S cfalse 
  &&(and.big seq(S) ==> rho_1 = rho_2 )equiv cfalse 
$

// $
//   // Rigid-Rigid
//   overline(sscope) tack alpha = beta = umultieq &-->_S overline(sscope) union overline(sscope)' tack alpha^beta = umultieq &#h1& "if" alpha, beta in srv(S) and overline(sscope)' in smineq(S, overline(sscope), alpha = beta) \

//   // Former-Rigid
//   overline(sscope) tack overline(alpha) tformer = beta = umultieq &-->_S overline(sscope) union overline(sscope)' tack (overline(alpha) tformer)^beta = umultieq and and.big_i alpha_i = tau_i && "if" beta in srv(S) and overline(sscope)' in smineq(S, overline(sscope), beta = overline(tau) tformer) \

//   // Amb-Rigid
//   overline(sscope) tack (psi approx alpha) = beta = umultieq &-->_S overline(sscope) union overline(sscope)' tack psi approx alpha approx beta = umultieq&& "if" beta in srv(S) and overline(sscope)' in smineq(S, overline(sscope), alpha = beta) \


//   // Amb-context
//   // This one is odd -- essentially in the solver we often want to ignore the ambivalent variables and just look at the head of the ambivalent type. 
//   overline(sscope) tack (psi approx alpha) = umultieq &-->_S overline(sscope)' tack (psi' approx alpha) = umultieq' and U &&"if" overline(sscope) tack psi = umultieq -->_S overline(sscope)' tack psi' = umultieq' and U \

//   // Former-Former

//   overline(sscope) tack overline(alpha_1) tformer = overline(alpha_2) tformer = umultieq &--> overline(sscope) tack overline(alpha_1) tformer = umultieq and and.big_i dot tack alpha_(1i) = alpha_(2i) \

//   // Clash
//   overline(sscope) tack rho_1 = rho_2 = umultieq &-->_S cfalse && head(rho_1) eq.not head(rho_2) and rho_1, rho_2 "are rigid" \
//   &&&and (and.big seq(S) ==> rho_1 = rho_2 )equiv cfalse
// $

#let sincon = textsf("incon")

Solver rules:
$
  #proof-tree(
    rule(
      $S; U; A ==> C --> S[sscope : A ==> shole]; U; C$,
      $"fresh" sscope$,
      // $(exists srv(S). and.big seq(S) and A) equiv ctrue$,
      name: [(PUSH-EQ)]
    )
  )

  #v2

  // The rule I naturally would come up with is below
  #proof-tree(
    rule(
      $S[sscope: A ==> exists overline(alpha), overline(beta). shole]; U; C --> S[exists overline(alpha). sscope: A ==> exists overline(beta). shole]; U; C$,
      $(exists overline(beta). U) "determines" overline(alpha)$,
      name: [(EQ-EX)]
    )
  )
  // We don't need to add seq(S) => ... to determines since the consistency is quantified over in 
  // the determines relation
  #v2

  // However, this differs from Oliver's rule which uses the domination relation to say the overline(alpha) is old. This is more procedural -- EMLTI uses determines as a 'semantic' relation for domination. 
  // #proof-tree(
  //   rule(
  //      $S[sscope: A ==> exists alpha, overline(beta). shole]; U; ctrue --> S[exists overline(alpha). sscope: A ==> exists overline(beta). shole]; U; ctrue$,
  //     $gamma in fv(exists overline(alpha), overline(beta). U)$,
  //     $forall i. space alpha_i scripts(prec)_U^* gamma$,
  //     name: [(EQ-EX-OLIVIER)]
  //   )
  // )
  // #v2

  // NOTE: we don't need to quantify the variables in eqs(S) in the equivalence below since implicitly they're universally quantified -- which is handled with the equiv statement
  #proof-tree(
    rule(
      $S[sscope: A ==> exists overline(alpha). shole]; U_1 and U_2; ctrue --> S; U_1; ctrue$,
      $overline(alpha), sscope \# U_1$,
      $(and.big seq(S), sscope ==> exists overline(alpha). U_2) equiv ctrue$,
      name: [(POP-EQ)]
    )
  )

  #v2

  // Again this rule is rather odd -- but clearly works. It captures that phi has escaped the current scope. Why does it work? If the equivalent is not true, then there is some assignment of a variable (not bound in overline(alpha)) that causes the constraint to fail. This is equivalent to saying that the equation is dominated by some older variable. This older variable causes the scope leakage. 
  #proof-tree(
    rule(
      $S[sscope : A ==> exists overline(alpha). shole]; U and overline(sscope)' tack umultieq; ctrue --> cfalse$,
      $sscope in overline(sscope)'$,
      $(and.big seq(S), sscope ==> exists overline(alpha). umultieq ) equiv.not ctrue$,
      name: [(EQ-SCOPE-ESCAPE)]
    )
  )

  #v2

  // This is the rule I would write
  // There is some young variable that relies on phi but is dominated by an older variable (leaking the scope).
  // #proof-tree(
  //     rule(
  //       $S[sscope : A ==> exists alpha, overline(alpha). shole]; U; ctrue --> cfalse$,
  //       $gamma in fv(exists overline(alpha). U)$,
  //       $alpha scripts(prec)_U^* gamma$,
  //       $sscope in seq_U (alpha)$,
  //       name: [(EQ-SCOPE-ESCAPE)]
  //     )
  // )

  // #v2 

  // #proof-tree(
  //   rule(
  //     $S; U; A ==> C --> sincon$,
  //     $$, 
  //     name: [(EQ-INCONSISTENT)] 
  //   )
  // )
$

// The last rule adds a new kind of state to the solver -- an inconsistent state. Such a rule could be used to handle absurdity (if we can bake that into the semantics of constraints somehow). 