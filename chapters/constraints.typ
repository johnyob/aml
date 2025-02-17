
#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

In this section, we define the constraint language. Following Pottier and Remy [??], our constraint language uses both expression variables and type variables. 

The syntax is given below. For composition we have $ctrue$, the trivially true constraint, $cfalse$, the unsatisfiable constraint, and conjunction $C_1 and C_2$. 
The equality constraint $tau_1 = tau_2$ asserts that the types $tau_1$ and $tau_2$ are equivalent. Similarly, the equality constraint between scopes $Psi_1 = Psi_2$ asserts that the two scopes $Psi_1$ and $Psi_2$ are equal. The existential constraint $exists alpha. C$ that binds the _flexible_ ($fflex$) type variable $alpha$ in $C$. The universal constraint $forall alpha. C$ that binds the _rigid_ ($frigid$) type variable $alpha$ in C. The scoped existential constraint $exists scopev. C$ introduces an existential scope variable $scopev$. 
The _implication_ constraint $eqname : tau_1 = tau_2 ==> C$ that assumes the assumptions $tau_1 = tau_2$ with name $eqname$ hold in $C$. The instance constraint $x <= tau$ (and substitued form $sigma <= tau$) asserts that the scheme of $x$ can be instantiated to the type $tau$. The definition and let constraints $cdef x : sigma cin C$ and $clet x : sigma cin C$ bind the scheme $sigma$ to $x$ in $C$, with the $clet$ constraint additionally asserting that $sigma$ is _satisfiable_ -- informally it has one or more instances and none of the bound rigid variables are _dangerous_. 

Like #aml, our constraint language distinguishes between flexible and rigid type variables.


Constraints are considered equivalent modulo alpha-renaming of all binders, including type, scope, equational, and expression variables.

#syntax(
  horizontal-spacing: 1.5cm,
  syntax-rule(name: [Constraints], $C in Con ::= &ctrue | cfalse | C and C \ 
  | &exists alpha. C | exists scopev. C | forall alpha. C \ 
  | &tau = tau | Psi = Psi | eqname : tau_1 = tau_2 ==> C \  
  | &cdef x : sigma cin C | x <= tau | sigma <= tau \ 
  | &clet x : sigma cin C 
  $),


  syntax-rule(name: [Constrained\ Type Schemes], $sigma ::= cforall(Theta, C, tau) $), 

  syntax-rule(name: [Quantifier Contexts], $Theta ::= dot | Theta, alpha :: f | Theta, scopev$),

  syntax-rule(name: [Environment Contexts], $Gamma ::= dot | Gamma, x : sigma$),

  syntax-rule(name: [Contexts], $Delta ::= dot | Delta, alpha :: f | Delta, scopev | Delta, eqname | Delta, x$),
)

Environment contexts $Gamma$ are similar to the type contexts $Gamma$ described in ??, removing all variable and equation binders and replacing type schemes with constrained type schemes $sigma$. We write $cdef Gamma cin C$ for the constraint:
$
  cdef dot cin C &= C \ 
  cdef Gamma, x : sigma cin C &= cdef Gamma cin cdef x : sigma cin C
$
We define $clet Gamma cin C$ symmetrically. 


_Well-formedness_. The constraint well-formedness judgement $Delta tack C ok$. We ensure all types under ambivalent scopes are rigid and assumptions $tau_1 = tau_2$ are rigid. The well-formedness rules are given in Figure ??. By implicitly translating $Delta$ into a type context $Gamma$ (defined in Chapter ??), we reuse the well-formedness judgements for types and scopes: $Delta tack tau ok, Delta tack tau rigid,$ and \ $Delta tack Psi ok$ from Chapter ??. 




#judgement-box($Delta tack sigma ok$, $Delta tack C ok$)
$
  #v2 
  
  #proof-tree(
    rule(
      $Delta tack ctrue ok$, 
      $$,
      name: [(True)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack cfalse ok$, 
      $$, 
      name: [(False)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack C_1 and C_2 ok$, 
      $Delta tack C_1 ok$, 
      $Delta tack C_2 ok$, 
      name: [(Conj)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack exists alpha. C ok$, 
      $Delta, alpha :: fflex tack C ok$, 
      $alpha disjoint Delta$, 
      name: [(Exists)]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Delta tack forall alpha. C ok$, 
      $Delta, alpha :: frigid tack C ok$, 
      $alpha disjoint Delta$, 
      name: [(Forall)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack exists scopev. C$, 
      $Delta, scopev tack C$, 
      $scopev disjoint Delta$,
      name: [(ExistsScope)]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Delta tack tau_1 = tau_2 ok$, 
      $Delta tack tau_1 ok $, 
      $Delta tack tau_2 ok $, 
      name: [(Equal)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack Psi_1 = Psi_2 ok$,
      $Delta tack Psi_1 ok $, 
      $Delta tack Psi_2 ok$,
      name: [(EqualScope)]
    )
  )

  #v2

  

  #proof-tree(
    rule(
      $Delta tack eqname : tau_1 = tau_2 ==> C ok$, 
      $Delta tack tau_1 = tau_2 rigid$, 
      $Delta, eqname tack C ok$, 
      $eqname disjoint Delta$,
      name: [(Impl)]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Delta tack cdef x : sigma cin C ok$, 
      $Delta tack sigma ok$, 
      $Delta, x tack C ok$, 
      $x disjoint Delta$, 
      name: [(Def)]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack x <= tau ok$, 
      $x in Delta$, 
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
      $x disjoint Delta$, 
      name: [(Let)]
    )
  ) 

  #v2 

  #proof-tree(
    rule(
      $Delta tack cforall(Theta, C, tau) ok$, 
      $Xi tack C ok$, 
      $Xi tack tau ok$,
      $Theta disjoint Delta$,
      label: $Xi = Delta, Theta$, 
      name: [(Scheme)]
    )
  )
$


_Semantics._ Having defined the syntax of constraints and given an informal description of their meaning. We now formally define the semantic interpretation of constraints. We begin with a definition of a _model_ $cal(M)$.

Our constraints are interpreted under a Herbrand universe, that is a finite tree model of _ground types_ ($gt$). We interpret _scopes_ as consistency bits ($kappa$) which are $ctrue$ if all equations in the scope are true under the current assignment. 

#syntax(
  horizontal-spacing: 2cm, 
  syntax-rule(name: [Ground Types], $gt in GTy ::= overline(gt) tformer | [kappa]gt$),
  syntax-rule(name: [Ground Instances], $gi in GInst ::= kappa tack gt$),
  syntax-rule(name: [Ground Schemes], $gs in GScm = cal(P)_"fin" (GInst)$),
  syntax-rule(name: [Consistency], $kappa ::= ctrue | cfalse$), 
  syntax-rule(name: [Assignments], $phi ::= dot | phi[alpha :: f  |-> gt] | phi[scopev |-> kappa] | phi[eqname |-> kappa]$), 
  syntax-rule(name: [Environments], $rho ::= dot | rho[x |-> gs]$), 
)

A ground assignment $phi$ is a _sort-preserving_ mapping from $cal(V)_s$ to the model $cal(M)_s$ for sorts $s in {Ty, Scope, EqName}$. We extend ground assignments to types and scopes using standard techniques. 

$
  phi_Ty (alpha) &= phi(alpha)  &&& phi_Scope (dot) &= ctrue \
  phi_Ty (overline(tau) tformer) &= overline(phi_Ty (tau)) tformer &&& phi_Scope (scopev) &= phi(scopev) \ 
  phi_Ty ([Psi] tau) &= [phi_Scope (Psi)] phi_(Ty \\ ::frigid) (tau) &#h(2cm)&& phi_Scope (Psi, eqname) &= phi_Scope (Psi) and phi(eqname) 
$

The interpretation of _scoped ambivalent types_ $[Psi]tau$ requires that $tau$ is interpreted as a _rigid_ type. To do so, we define a _$f$-restriction_ on the assignment $phi$ to only contain mapping for type variables for a given flexibility $f$. 
$
  (dot)_(\\ ::f) &= dot \ 
  (phi[alpha :: f' |-> gt])_(\\ ::f) &= cases(
    (phi_(\\ ::f))[alpha :: f' |-> gt] wide&"if" f = f', 
    phi_(\\ ::f) &"otherwise"
  )\
  (phi[\_])_(\\ ::f) &= (phi_(\\ ::f))[\_]
$ 

_Remark._ We often implicitly interpret consistency bits in the standard boolean model $bb(2)$. 

Mimicking #aml, our ground types have an equational theory with the following axioms:

#comment[TODO: center these equations (ignoring side condition)]
$
  [kappa](overline(gt) tformer) &= overline([kappa]gt) tformer &wide wide &"if" arity(tformer) > 0\ 

  [kappa_1][kappa_2]gt &= [kappa_1 and kappa_2] gt \ 

  [ctrue] gt &= gt \

  [cfalse] gt_1 &= [cfalse] gt_2
$
#comment[TODO: explain why the type system doesnt have the S4 rule. i.e concatenating scopes is hard for the solver, but fine for the constraint semantics. So we permit the rule here.]

Our semantics handle implication constraints in differently to the _natural semantics_ of implications. Instead we treat implications as _binders_ for equations ($eqname : tau_1 = tau_2$). Adding an equation to the context may affect the consistency ($kappa$). If we are in a consistent context, then it follows that only reflexive equalities have been introduced. Otherwise we are in an inconsistent context. Consistency affects the types we can introduce in existential binders, as we explain later. 

An _environment_ $rho$ is a partial function from expression variables $x in varset(Exp)$ to _ground type schemes_ $gs in GScm$ -- a set of consistency and ground type pairs $kappa tack gt$, known as a _ground instance_, which reflects that the scheme was instantiated to $gt$ under the consistency $kappa$. 


The satisfiability judgement for constraints $kappa, phi, rho tack C$ is given in Figure ??. We read $kappa, phi, rho tack C$ as: _in the environment $rho$ with consistency $kappa$, the assignment $phi$ satisfies the constraint $C$_. Our satisfiability judgement is syntax-directed, permitting a trivial inversion theorem. 


#judgement-box($kappa, phi, rho tack C $)
$
  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack ctrue$, 
      "",
      name: [(True)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack C_1 and C_2$,
      $kappa, phi, rho tack C_1$,
      $kappa, phi, rho tack C_2$,
      name: [(Conj)]
    )
  )


  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack exists alpha. C$, 
      $kappa ==> consistent(gt)$, 
      $kappa, phi[alpha :: fflex |-> gt], rho tack C$,
      $alpha disjoint phi$, 
      name: [(Exists)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack exists scopev. C$, 
      $kappa ==> kappa'$, 
      $kappa, phi[scopev |-> kappa'], rho tack C$, 
      $scopev disjoint phi$, 
      name: [(ExistsScope)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack forall alpha. C$, 
      $forall gt$, 
      $kappa and consistent(gt), phi[alpha :: frigid |-> gt], rho tack C$, 
      $alpha disjoint phi$, 
      name: [(Forall)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack tau_1 = tau_2$,
      $phi(tau_1) = phi(tau_2)$, 
      name: [(Equal)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack Psi_1 = Psi_2$,
      $phi(Psi_1) = phi(Psi_2)$, 
      name: [(EqualScope)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack eqname : tau_1 = tau_2 ==> C$, 
      $kappa and kappa', phi[eqname |-> kappa'], rho tack C$, 
      $eqname disjoint phi$, 
      label: [$kappa' = (floor(phi_(\\ ::frigid)(tau_1)) = floor(phi_(\\ ::frigid)(tau_2)))$],
      name: [(Impl)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack cdef x : sigma cin C$, 
      $kappa, phi, rho[x |-> (phi, rho) sigma] tack C$, 
      $x disjoint rho$, 
      name: [(Def)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack x <= tau$, 
      $kappa tack phi(tau) in rho(x)$, 
      name: [(VarInst)]
    )
  )


  #h1

  #proof-tree(
    rule(
      $kappa, phi, rho tack sigma <= tau$, 
      $kappa tack phi(tau) in (phi, rho) sigma$, 
      name: [(SchemeInst)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $kappa, phi, rho tack clet x : sigma cin C$, 
      $kappa, phi, rho tack exists sigma$, 
      $kappa, phi, rho[x |-> (phi, rho) sigma] tack C$, 
      $x disjoint rho$,
      name: [(Let)]
    )
  ) 
$

// Explaination of all of the rules

// Trivial constraints
The (True) judgement states that $ctrue$ is a tautology, that is, holds under every assignment. No such rule matches $cfalse$, which means $cfalse$ is unsatisfiable. (And) requires each of the conjucts to be satisfiable under the assignment. 
// Equalities 
The (Equal) and (EqualScope) simply state that the equalities are satisfiable if they are satisfiable within the model under the current assignment $phi$. 

// Binders 
(Exists) allows type variables $alpha$ to denote arbitrary ground types $gt$ in $C$ _provided_ they are consistent with $kappa$. We say a ground type $gt$ is _consistent_ 
if all scopes in $gt$ are $ctrue$. 
$
  consistent(overline(gt) tformer) &= and.big_i consistent(gt_i) \ 
  consistent([kappa]gt) &= kappa and consistent(gt)
$
Similarly (ExistsScope) permits one to bind $scopev$ to an arbitrary ground scope $kappa'$ if $kappa'$ is consistent with $kappa$, that is, $kappa$ entails (or implies) $kappa'$. (Forall) checks that $C$ is satisfiable for all possible assignments to $alpha$. It is worth noting that (Forall) modifies the _consistency_ when interpreting $C$ the assignment $gt$ may be inconsistent. Without modfiying the consistency, tautologies such as $forall alpha. exists beta. alpha = beta$ would be unsatisfiable. 

// Implications 
As explained above, the satisfiability judgement takes into account the consistency (or inconsistency) of the current context. The only way to introduce an inconsistency is 
is to assume an equality hypothesis constraint between two incompatible types. The equality hypothesis must be between two _rigid_ types, so we use a $frigid$-restriction of $phi$ to interpret the equality. We also have to _erase_ the scopes that may appear $tau_1$ and $tau_2$ since rigid variables may be instantiated with ground _scoped ambivalent types_. 
We additionally bind the consistency of the assumption to the equation name $eqname$ so that we may refer to it in $C$. 
It is worthwhile to note that since rigid variables are _universally quantified_, the equality $tau_1 = tau_2$ may be true or false depending on the assignment to a given rigid variable. When reasoning about implications, this produces two disjoint derivations depending on the value of $kappa$. 

// Schemes (Inst, Def, Let)
(VarInst) check whether $tau$ is an instance of the type scheme bound to $x$. Since all constrained type schemes are interpreted as sets of ground instances, then the interpretation of $tau$ with the current consistency forms an _instance_ which we may check with set membership. (SchemeInst) is simply the substituted rule for (VarInst). 
// Interpretation
The interpretation of a constrained type scheme $cforall(Theta, C, tau)$ under the assignment $phi$ is the set of ground instances $kappa' tack phi'(tau)$ which satisfy $C$, where $phi'$ extends $phi$ with $Theta$ and $phi'$ has to pick only consistent assignments when $kappa'$ is consistent:
$
  (phi, rho)(cforall(Theta, C, tau)) = { kappa' tack phi'(tau) :
    cases(delim: #none, 
      kappa' tack phi' >= phi : Theta \
      and kappa'\, phi'\, rho tack C) } \

  #v2

  #proof-tree(
    rule(
      $kappa tack phi >= phi : dot$, 
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $kappa tack phi'[alpha :: f |-> gt] >= phi : Theta, alpha :: f$, 
      $kappa ==> consistent(gt)$, 
      $kappa tack phi' >= phi : Theta$, 
      $alpha disjoint phi$
    )
  )

  #v2 

  #proof-tree(
    rule(
      $kappa tack phi'[scopev |-> kappa'] >= phi : Theta, scopev$, 
      $kappa ==> kappa'$, 
      $kappa tack phi' >= phi : Theta$, 
      $scopev disjoint phi$
    )
  )
$

// Def constraints
(Def) has the semantic interpretation as an _explicit substitution_ form, interpreting the scheme $sigma$ under $(phi, rho)$ and binding it to $x$ in $C$. With this interpretation, we have the following equivalence law:
$
  cdef x : sigma cin C equiv C[x := sigma]
$
// Let constraints
The (Let) rule is similar to (Def), but checks that the constrained type scheme $sigma$ is _satisfiable_ (denoted $kappa, phi, rho tack exists sigma$). Let $sigma = cforall(Theta, C, tau)$, there are two conditions $sigma$ to be satisfiable:
+ The interpretation of $sigma$ must be non-empty, that is to say $sigma$ has at least one instance. 
+ All rigid variables are polymorphic in $C$. 
+ All rigid variables bound in $Theta$ are not _dangerous_. 

// (1) and (2). 
Without loss of generality, we may write $Theta$ as $overline(alpha :: frigid), overline(beta :: fflex), overline(scopev)$. To check whether $sigma$ has an instance, it is sufficient to check $exists gamma. sigma <= gamma$ is satisfiable. To check whether all rigid variables are polymorphic in $C$, it is sufficient to check $forall overline(alpha). exists overline(beta), overline(scopev). C$ is satisfiable. We note that this constraint entails $exists gamma. sigma <= gamma$, so it is sufficient to only check (2) instead of checking (1) and (2). 

// (3)
Ensuring all rigid variables bound in $Theta$ are not dangerous is harder to define.
A type scheme is not dangerous, i.e _safe_, if all rigid variables are safe in the type scheme.  
#let safe = textsf("safe")
$
  #proof-tree(
    rule(
      $kappa, phi, rho tack cforall(Theta, C, tau) safe$, 
      $forall alpha in Theta \\ ::frigid$, 
      $kappa, phi, rho tack alpha in cforall(Theta, C, tau) safe $
    )
  )
$

To define safety of a single rigid variable, we define what it means to be _ dangerous_ and then take the negation of that property. We begin by extending the definition of $dangerous$ to ground types. 
$
  dangerous(overline(gt) tformer) &= union.big_i dangerous(gt_i) \ 
  dangerous([kappa]gt) &= cases(
    dangerous(gt) &"if" kappa = ctrue, 
    cal(P)(gt) &"if" kappa = cfalse
  )
$
where $cal(P)(gt)$ for the set of all subterms that appear in $gt$. 
$
  cal(P)(overline(gt) tformer) &= { overline(gt) tformer } union union.big_i cal(P)(gt_i) \ 
  cal(P)([kappa]gt) &= { [kappa]gt } union cal(P)(gt)
$

A rigid variable $alpha$ is dangerous in $cforall(Theta, C, tau)$ under $kappa, phi, rho$ if for every assignment to $alpha$, the interpretation of $alpha$ occurs in a dangerous position in $tau$ provided $C$ is satisfied. We formally state this below:

$
  #proof-tree(
    rule(
      $kappa, phi, rho tack alpha in cforall((Theta, alpha :: frigid), C, tau) dangerous$, 
      $forall gt. $,
      $overbrace(kappa and consistent(gt), kappa') tack overbrace(phi'[alpha :: frigid |-> gt], phi'') >= phi : Theta, alpha$, 
      $kappa', phi'', rho tack C$, 
      $gt in dangerous(phi''(tau))$, 
    )
  )
$

We now define $kappa, phi, rho tack alpha in sigma safe$ as the negation of the property above:
$
  #proof-tree(
    rule(
      $kappa, phi, rho tack alpha in sigma safe$, 
      $not(kappa, phi, rho tack alpha in sigma dangerous)$
    )
  )
$

Having defined formal properties for (1), (2), and (3), we may now formally define the satisfiability of $sigma$, written $kappa, phi, rho tack exists sigma$. 
$
  #proof-tree(
    rule(
      $kappa, phi, rho tack exists underbrace((cforall((overline(alpha :: frigid), overline(beta :: fflex), overline(scopev)), C, tau)), sigma)$, 
      $kappa, phi, rho tack forall overline(alpha). exists overline(beta), overline(scopev). C$, 
      $kappa, phi, rho tack sigma safe$

    )
  )
$

#comment[Q: Does this affect the well-foundedness of satisfiability?]

== Constraint Generation

We introduce a function $[| e : alpha |]$, which translates the expression $e$ and type variable $alpha$ to a constraint. Assuming $e$ is well-formed under $Delta$ ($Delta tack e ok $), then $[| e : alpha |]$ is well-formed under $Delta$ and $alpha$ ($alpha :: fflex, Delta tack [|e : alpha|] ok$). We assume a standard definition for well-formedness of expressions under a context $Delta$, ensuring all terms and annotations are well-scoped. 

// Explaination of [| - |]
The function $[| - |]$ is defined in Figure ??. This function produces a constraint $C$ which is satisfiable if and only if $e$ is well-typed with type $alpha$. Variables generate an instantiation constraint. Functions generate a constraint that bind two fresh flexible type variables for the argument and return types and uses the $cdef$ constrain to bind the argument in the constraint generated for the body of the function. Function application binds two fresh flexible type variables for the function and argument types and ensures $alpha$ is the return type of the function type. Let expressions generate a flexible polymorphic $clet$ constraint. The abbreviation $paren.double e paren.double.r$ is a _principal constrained type scheme_ for $e$: its intended interpretation is the set of all ground types that $e$ admits. 
Primitive constructors such as $erefl$ and $()$ generate specialized instantiation constraints for their corresponding types. 

The univerally quantified expression binds the rigid variable $beta$ in $e$; morally the constriant generated should be of the form:
$
  [| efun (etype beta) -> e : alpha |] = (forall beta. exists gamma. [| e : gamma |]) and (exists beta. [| e: alpha |])
$
This is because we need to check $e$ is well-typed for every instantiation of $beta$
and then instantiate the type scheme to have the type $alpha$. However, this generation rule would compromise the linear time and space complexity of constraint generation since it generates two constraints for $e$. To avoid this problem we make use of _principal rigid constrained type schemes_ $paren.double e paren.double.r_beta$ -- these are similar to _principal constrained type schemes_ but they additionally bind a rigid variable $beta$. The semantics of rigid constrained type schemes ensure $forall beta. exists gamma. [| e: gamma |]$ holds and we can check $exists beta. [| e : alpha |]$ by instantiating the constrained type scheme to $alpha$.

Annotations bind a flexible variable for the _inner_ type of $e$. However, unlike #aml 
we cannot _erase_ scopes in constraints. The solution is introduce unshared scopes on two instances of the annotation. We do so by defining the constriant $ceil(tau) = alpha$ which states that $alpha$ is equal to $tau$ with some scopes _inserted_ in $tau$. 
$
  (ceil(beta) = alpha) &= exists scopev. [scopev]beta = alpha \ 
  (ceil(tformer) = alpha) &= exists scopev. [scopev]tformer = alpha \ 
  (ceil(overline(tau) tformer) = alpha) &= exists overline(beta). overline(beta) tformer = alpha and and.big_i ceil(tau_i) = beta_i 
$

Match expressions check the matchee has the type $tau_1 = tau_2$ -- using an inlined version of the annotation rule. We then bind the equation to a fresh equation name in the body of the match case. The equation cannot leak the scope of implication conclusion since $alpha$ is bound outside the generated constraint. 
$
  
  [| x : alpha |] &= x <= alpha \ 
  [| efun x -> e : alpha |] &= exists alpha_1 alpha_2. cdef x: alpha_1 cin [| e : alpha_2 |] and alpha = alpha_1 -> alpha_2 \ 
  [| e_1 space e_2 : alpha |] &= exists alpha_1, alpha_2. [| e_1 : alpha_1 |] and [| e_2 : alpha_2 |] and alpha_1 = alpha_2 -> alpha  \ 
  [| clet x = e_1 cin e_2 : alpha |] &= clet x : paren.l.double e_1 paren.r.double cin [| e_2 : alpha |] \ 
  [| efun (etype beta) -> e : alpha |] &= clet x : paren.l.double e paren.r.double_beta cin x <= alpha \ 
  [| (e : tau) : alpha |] &= alpha = ceil(tau) and exists beta. beta = ceil(tau) and [| e : beta |] \ 
  [| erefl : alpha |] &= exists alpha_1. alpha = (alpha_1 = alpha_1) \ 
  [| () : alpha |] &= exists scopev. alpha = [scopev]tunit \
  [| ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : alpha |] &= (exists beta. beta = ceil(tau_1 = tau_2) and [| e_1 : beta |]) and eqname : tau_1 = tau_2 ==> [| e_2 : alpha |] \
  paren.l.double e paren.r.double &= forall alpha :: fflex. [| e : alpha |] => alpha \ 
  paren.l.double e paren.r.double_alpha &= forall alpha :: frigid, beta :: fflex. [| e : beta |] => beta 
$



== Metatheory 

_Equivalences_. Our later technical developments will rely on establishing equivalences between constraints, so we now define notions of _entailment_ and _equivalence_. 

A constraint $C_1$ entails $C_2$, written $C_1 tack.double C_2$, if every context that satisfies $C_1$ also satisfies $C_2$. Similarly, equivalence $C_1 equiv C_2$ holds if the property is bidirectional.

In our semantics, the $cdef$ form is an _explicit substitution_. More formally, the semantics satisfy the equivalence law:
$
  cdef x : sigma cin C equiv C[x := sigma]
$
Instantiation constraints satisfy the equivalence law:
$
  (forall overline(alpha), overline(beta). C => gamma) <= delta equiv exists overline(alpha), overline(beta). C and gamma = delta
$
$clet$ forms are equivalent to $cdef$ constraints that check the satisfiability of the constrainted type scheme:
$
  clet x : underbrace((forall overline(alpha), overline(beta). C_1 => gamma), sigma)  cin C_2 equiv (forall overline(alpha). exists overline(beta). C_1) and cdef x : sigma cin C_2 
$

