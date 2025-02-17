
#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

#show: thmrules

In this section, we define the constraint language. Following Pottier and Rémy [??], our constraint language uses both expression variables and type variables. 

// Syntax + informal meaning
The syntax is given below. For composition we have $ctrue$, the trivially true constraint, $cfalse$, the unsatisfiable constraint, and conjunction $C_1 and C_2$. 
The equality constraint $tau^kappa_1 = tau^kappa_2$ asserts that the types $tau^kappa_1$ and $tau^kappa_2$ are equivalent. The existential constraint $exists alpha :: kappa. C$ that binds the _flexible_ ($fflex$) type variable $alpha$ of kind $kappa$ in $C$. The universal constraint $forall alpha :: kappa. C$ that binds the _rigid_ ($frigid$) type variable $alpha$ of kind $kappa$ in $C$. The _implication_ constraint $eqname : tau_1 = tau_2 => C$ that assumes the assumptions $tau_1 = tau_2$ with name $eqname$ hold in $C$. The let constraint $clet x = forall overline(alpha :: kappa). lambda beta. C_1 cin C_2$ binds the _rigid constraint abstraction_ $forall overline(alpha :: kappa). lambda beta. C_1$ to $x$ in $C_2$ -- ensuring the abstraction is _satisfiable_ (defined later). A constraint abstraction $forall overline(alpha :: kappa). lambda beta. C$ can intuively be seen as a function which when applied to some type $tau$ returns $exists overline(alpha :: kappa). C[beta := tau]$#footnote([This substitution is only valid if all occurances of $overline(alpha)$ are not _dangerous_ in $C$ or $tau$]). Constraint abstractions can be applied using the constraint $x space tau$ which applies $tau$ to the abstraction bound to $x$.  

Like #aml, our constraint language distinguishes between flexible and rigid type variables.
Constraints are considered equivalent modulo alpha-renaming of all binders, including type, scope, equational, and expression variables.

#syntax(
  syntax-rule(
    name: [Constraints],
    collection: Con, 
    $C$,
    $ctrue | cfalse | C and C$, 
    $exists alpha :: kappa. C | forall alpha :: kappa. C | tau^kappa = tau^kappa$, 
    $ eqname : tau_1 = tau_2 => C$, 
    $clet x = Lambda cin C | x space tau$,
  ),

  syntax-rule(
    name: [Constraint Abstractions], 
    collection: ConAbs, 
    $Lambda$, 
    $forall overline(alpha :: kappa). lambda beta. C$
  ),

  syntax-rule(
    name: [Constraint Contexts], 
    collection: ConCtx,
    $Delta$, 
    $emptyset | Delta, alpha ::^phi kappa | Delta, eqname | Delta, x$
  )
)

_Well-formedness_. The constraint well-formedness judgement $Delta tack C ok$. We ensure all types under ambivalent scopes are rigid and assumptions $tau_1 = tau_2$ are rigid. The well-formedness rules are given in Figure ??. By implicitly translating $Delta$ into a type context $Gamma$ (defined in Chapter ??), we reuse the well-formedness judgements for types $Delta tack tau :: kappa space phi$ from Chapter ??. 

#judgement-box($Delta tack C ok$)
$

  
  #proof-tree(
    rule(
      $Delta tack ctrue ok$, 
      $$,
      name: [TrueWF]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack cfalse ok$, 
      $$, 
      name: [FalseWF]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack C_1 and C_2 ok$, 
      $Delta tack C_1 ok$, 
      $Delta tack C_2 ok$, 
      name: [ConjWF]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack exists alpha :: kappa. C ok$, 
      $Delta, alpha ::^fflex kappa tack C ok$, 
      $alpha disjoint Delta$, 
      name: [ExistsWF]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Delta tack forall alpha :: kappa. C ok$, 
      $Delta, alpha ::^frigid kappa tack C ok$, 
      $alpha disjoint Delta$, 
      name: [ForallWF]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Delta tack tau^kappa_1 = tau^kappa_2 ok$, 
      $Delta tack tau^kappa_1 :: kappa$, 
      $Delta tack tau^kappa_2 :: kappa$, 
      name: [EqualWF]
    )
  )

  #v2
  

  #proof-tree(
    rule(
      $Delta tack eqname : tau_1 = tau_2 => C ok$, 
      $Delta tack tau_1, tau_2 :: ty frigid$, 
      $Delta, eqname tack C ok$, 
      $eqname disjoint Delta$,
      name: [ImplWF]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Delta tack clet x = Lambda cin C ok$, 
      $Delta tack Lambda ok$, 
      $Delta, x tack C ok$, 
      $x disjoint Delta$, 
      name: [LetWF]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Delta tack x space tau ok$, 
      $x in Delta$, 
      $Delta tack tau :: ty$,
      name: [AppWF]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Delta tack forall overline(alpha :: kappa). lambda beta. C ok$, 
      $Delta, overline(alpha ::^frigid kappa), beta ::^fflex ty tack C ok$, 
      $overline(alpha), beta disjoint Delta$,
      name: [AbsWF]
    )
  )
$


_Semantics._ Having defined the syntax of constraints and given an informal description of their meaning, we now present a formal semantic interpretation of constraints. 

// Open model
Unlike Pottier and Rémy we give our semantics using an _open_ finite tree model in which types may contain variables, rather than Herbrand universe -- a _ground_ finite tree model. The choice is made purely to simply the proofs of metatheoretic properties; we conjecture that the corresponding semantics using a ground model is equivalent to our semantics. 

Key to our presentation of an _open_ semantics is our notion of an _ordered assignment_; which define the scope of existential variables and controls the free variables of their solution. 
#syntax(
  syntax-rule(
    name: [Assignments], 
    collection: Assn,
    $Phi$,
    $emptyset | Phi, alpha ::^phi kappa | Phi, alpha ::^fflex kappa := tau^kappa$, 
    $Phi, eqname : tau = tau | Phi, x : sigma$), 
)

// Assignment solutions 
Like typing contexts $Gamma$, assignments $Phi$ are ordered and contain declarations of polymorphic variables ($alpha ::^phi kappa$), equation ($eqname : tau_1 = tau_2$) and term variable bindings $(x : sigma)$. Unlike typing contexts, assignments also contain declarations of _existential (flexible) type variables_ with solutions ($alpha ::^fflex kappa := tau^kappa$). It is interesting to note that all typing contexts $Gamma$ are assignments. 

// Order
The well-formedness rules of assignments (Figure ??) not only prohibit duplicate  declarations, but also enforce order: if $Phi = Phi_L, alpha ::^frigid kappa := tau^kappa, Phi_R$, the solution type $tau^kappa$ must be well-formed under $Phi_L$. Consequentialy, circularity is ruled out: $alpha ::^fflex ty := beta, beta ::^fflex ty := alpha$ is ill-formed. 

#judgement-box($Phi tack tau^kappa :: kappa space phi$, $Phi tack sigma scm$, $Phi assn$)

$

  #proof-tree(
    rule(
      $Phi tack alpha :: kappa space phi'$,
      $alpha ::^phi kappa in Phi$, 
      $phi <= phi'$, 
      name: [VarAssnWF]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Phi tack alpha :: kappa space fflex$, 
      $alpha ::^fflex kappa := tau^kappa in Phi$, 
      name: [SolvedVarAssnWF]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Phi tack overline(tau) tformer :: ty phi$,
      $forall i, space Phi tack tau_i :: ty phi$, 
      name: [TyConAssnWF]
    )
  )

  #h1


  #proof-tree(
    rule(
      $Phi tack [Psi] tau :: ty$,
      $Phi tack Psi :: scope$,
      $Phi tack tau :: ty frigid$, 
      name: [AmbAssnWF]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Phi tack emptyset :: scope$,
      $$, 
      name: [EmpScAssnWF]
    )
  )

  #h1


  #proof-tree(
    rule(
      $Phi tack Psi, eqname :: scope$,
      $Phi tack Psi :: scope$,
      $eqname in dom(Phi)$, 
      name: [ConsScAssnWF]
    )
  )


  #v2

  #proof-tree(
    rule(
      $Phi tack tau scm$, 
      $Phi tack tau :: ty$, 
      name: [AssnScmTy]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Phi tack tforall(alpha :: kappa) sigma scm$,
      $Phi, alpha ::^phi kappa tack sigma scm$,
      $alpha disjoint Phi$, 
      name: [AssnScm$forall$]
    )
  )

  #v2

  #proof-tree(
    rule(
      $emptyset assn$, 
      $$,
      name: [EmpAssn] 
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Phi, alpha ::^phi kappa assn$, 
      $Phi assn$, 
      $alpha disjoint Phi$, 
      name: [TyVarAssn]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Phi, alpha ::^fflex kappa := tau^kappa assn$, 
      $Phi assn$, 
      $Phi tack tau^kappa :: kappa$, 
      $alpha disjoint Phi$, 
      name: [SolvedTyVarAssn]
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Phi, x : sigma assn$, 
      $Phi assn$, 
      $Phi tack sigma scm$, 
      $x disjoint Phi$, 
      name: [VarAssn]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Phi, eqname : tau_1 = tau_2 assn$, 
      $Phi assn$, 
      $Phi tack tau_1, tau_2 :: ty frigid$,  
      $eqname disjoint Phi$, 
      name: [EqAssn]
    )
  )

$

// Substitution
Assignments may be viewed as parallel substitutions on types, substituting solved existential variables. We write ${Phi}tau^kappa$ for $Phi$ applied as a substitution to type $tau^kappa$; this operation is defined in Figure ??. We extend this substitution to type schemes in the typical capture avoiding way. 

#judgement-box(${Phi}tau^kappa : Ty$, ${Phi}sigma : Scm$)
#[
  #show math.equation: set align(end)
$
  {Phi} alpha &= {Phi}tau^kappa &#h(2.8cm)"if" alpha ::^fflex kappa := tau^kappa in Phi\ 
  {Phi} alpha &= alpha &"otherwise" \
  {Phi} overline(tau) tformer &= overline({Phi}tau) tformer \ 
  {Phi} [Psi]tau &= [{Phi}Psi]({Phi}tau) \ 

  {Phi}emptyset &= emptyset \ 
  {Phi}(Psi, eqname) &= {Phi}Psi, eqname \ 
  {Phi}(tforall(alpha :: kappa) sigma) &= tforall(alpha :: kappa) {Phi}sigma &"if" alpha in.not dom(Phi)

$
]

We write $floor(Phi)$ for the typing context produced by erasing all solutions from $Phi$. Such a 
function permits us to re-use relations defined in Chapter ??, such as the equivalence relation for types or the #aml instantiation relation. 
#judgement-box($floor(Phi) : Ctx$)
$
  floor(emptyset) &= emptyset \ 
  floor(Phi\, alpha ::^phi kappa) &= floor(Phi), alpha ::^phi kappa \ 
  floor(Phi\, alpha ::^fflex kappa := tau^kappa) &= floor(Phi) \ 
  floor(Phi\, eqname : tau_1 = tau_2) &= floor(Phi), eqname : tau_1 = tau_2 \ 
  floor(Phi\, x : sigma) &= floor(Phi), x : {Phi}sigma
$

The satisfiability judgement for constraints $Phi tack C$ is given in Figure ??. We read $Phi tack C$ as: _the assignment $Phi$ satisfies the constraint $C$_. Our satisfiability judgement is syntax-directed, permitting a trivial inversion theorem. 

#judgement-box($Phi tack C$, $Phi tack Lambda => sigma$)
$

  #proof-tree(
    rule(
      $Phi tack ctrue$, 
      "",
      name: [True]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Phi tack C_1 and C_2$,
      $Phi tack C_1$,
      $Phi tack C_2$,
      name: [Conj]
    )
  )


  #v2

  #proof-tree(
    rule(
      $Phi tack exists alpha :: kappa. C$, 
      $Phi tack tau^kappa :: kappa$, 
      $Phi, alpha ::^fflex kappa := tau^kappa tack C$,
      $alpha disjoint Phi$, 
      name: [Exists]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Phi tack forall alpha :: kappa. C$, 
      $Phi, alpha ::^frigid kappa tack C$, 
      $alpha disjoint Phi$, 
      name: [Forall]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Phi tack tau^kappa_1 = tau^kappa_2$,
      $Phi tack tau^kappa_1, tau^kappa_2 :: kappa$,
      $floor(Phi) tack {Phi}tau_1 = {Phi}tau_2$, 
      name: [Equal]
    )
  )
  #v2

  #proof-tree(
    rule(
      $Phi tack eqname : tau_1 = tau_2 => C$, 
      $Phi tack tau_1, tau_2 :: ty frigid$, 
      $Phi, eqname : tau_1 = tau_2 tack C$, 
      $eqname disjoint Phi$, 
      name: [Impl]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Phi tack clet x = Lambda cin C$, 
      $Phi tack Lambda => sigma$, 
      $Phi, x : sigma tack C$,
      $x disjoint Phi$, 
      name: [Let]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Phi tack x space tau$, 
      $Phi tack tau :: ty$,
      $x : sigma in Phi$,
      $floor(Phi) tack {Phi}sigma <= {Phi}tau$, 
      name: [App]
    )
  )


  #v2

  #proof-tree(
    rule(
      $Phi tack forall overline(alpha :: kappa). lambda beta.  C => tforall(overline(alpha :: kappa)\, overline(gamma :: kappa)) tau$, 
      $overline(alpha), overline(gamma), beta disjoint Phi$,
      $Phi' tack tau :: ty$, 
      $Phi', beta ::^fflex ty := tau tack C$,
      $overline(alpha) disjoint dangerous(tau)$,
      label: $Phi' = Phi, overline(alpha ::^frigid kappa), overline(gamma ::^fflex kappa)$, 
      name: [Abs]
    )
  )
$

// Explaination of all of the rules

// Trivial constraints
The (True) judgement states that $ctrue$ is a tautology, that is, holds under every assignment. No such rule matches $cfalse$, which means $cfalse$ is unsatisfiable. (Conj) requires each of the conjuncts to be satisfiable under the assignment. 
// Equalities 
The (Equal) rule simply states that the equality is satisfiable if the two substituted types are equivalent under $floor(Phi)$. 
// Binders 
(Exists) allows type variables $alpha$ to denote some arbitrary type $gt$ in $C$ _provided_ they are well-formed in $Phi$. (Forall) checks that $C$ is satisfiable with $alpha$ being polymorphically bound in $Phi$.  
// Implications 
(Impl) interprets implications as simply binding the equality $tau_1 = tau_2$ to the name $eqname$ in $C$. The equality hypothesis must be between two _rigid_ types, which we check using the well-formedness judgement for types.  

// Abstractions
A let constraint $clet x = forall overline(alpha :: kappa). lambda beta. C_1 cin C_2$
binds the rigid variables $overline(alpha :: kappa)$ and a flexible type variable $beta$ in $C_1$, rather like an existential constraint. The type scheme assigned to $x$ in $C_2$ is obtained by 
generalising the type variables appearing the solution of $beta$. This generalization, much like #aml, requires that the rigid variables $overline(alpha)$ are polymorphic _and_ do not occur in dangerous positions within $beta$'s solution.  
The application rule (App) checks whether $tau$ can be applied to the constraint abstraction bound to $x$. Since all constraint abstractions are interpreted as #aml type schemes, this is ensured by verifying that $tau$ is an instance of the type scheme bound to $x$. 


== Constraint Generation

We introduce a function $[| e : alpha |]$, which translates the expression $e$ and type variable $alpha$ to a constraint. Assuming $e$ is well-formed under $Delta$ ($Delta tack e ok $), then $[| e : alpha |]$ is well-formed under $Delta$ and $alpha$ ($alpha ::^fflex ty, Delta tack [|e : alpha|] ok$). We assume a standard definition for well-formedness of expressions under a context $Delta$, ensuring all terms and annotations are well-scoped. 

// Explaination of [| - |]
The function $[| - |]$ is defined in Figure ??. This function produces a constraint $C$ which is satisfiable if and only if $e$ is well-typed with type $alpha$. 

// Variables / primitives
Variables generate an instantiation constraint. Primitive constructors such as $erefl$ and $()$ generate specialized instantiation constraints for their corresponding types. 

// Functions
Functions generate a constraint that bind two fresh flexible type variables for the argument and return types. They use a $clet$ constraint to bind the argument in the constraint generated for the body of the function. This $clet$ constraint is _monomorphic_ since $alpha_3$ is fully constrained by type variables defined outside the abstraction's scope and therefore cannot be generalized. 
Function application binds two fresh flexible type variables for the function and argument types and ensures $alpha$ is the return type of the function type. 


// Let expressions 
Let expressions generate a polymorphic $clet$ constraint. The abbreviation $paren.double e paren.double.r$ is a _principal constrained type scheme_ for $e$: its intended interpretation is the set of all types that $e$ admits. 

// TFun expressions
The univerally quantified expression binds the rigid variable $beta$ in $e$. 
We need to ensure that the introduced is used _abstractly_ within the expression, and then instantiate $beta$ ??. 
This gives us the following constraint:
$
  [| efun (etype beta) -> e : alpha |] = clet x = forall beta :: ty. lambda gamma. [| e : gamma |] cin x space alpha
$
In the constraint abstraction, $beta$ is treated as a rigid variable, meaning it cannot be unified with an arbitrary type. This restriction prevents ill-typed programs such as: $efun (etype alpha) -> (efun x -> x : alpha -> alpha) space ()$. Within the body of the let constraint, we instantiate $beta$, ensuring that the resulting instantiation of the entire type scheme (produced by generalising $gamma$) is equal to $alpha$. The semantics of the let constraint further ensure $beta$ is not used dangerously in $gamma$. We write define the _rigid principal constrained type scheme_ for $e$, written $paren.l.double forall beta. e paren.r.double$, as: $forall beta :: ty. lambda gamma. [| e : gamma |]$. This behaves similarly to the principal constrained type scheme $paren.l.double e paren.r.double$ but it additionally binds the rigid variable $beta$. 

// Annotations
Annotations bind a flexible variable for the _inner_ type of $e$. We introduce a constraint alias $alpha = ceil(tau)$
that asserts $alpha$ is a _consistent instance_ of the rigid type $tau$. We define this alias using the _scope insertion_ function $ceil(tau)$ (defined in ??). Specifically, 
#[

  #show math.equation: set align(end)
$
  (alpha = ceil(tau)) &= exists cal(S). alpha = tau' &#h(2.8cm)"where" ceil(tau) = cal(S) triangle.r.small tau'
$ 
]

// Match expressions
Finally, match expressions check the matchee has the type $tau_1 = tau_2$, re-using the constraint generation rule for annotations. We then bind the equation to a fresh equation name in the body of the match case. The equation cannot leak the scope of implication conclusion since $alpha$ is bound outside the generated constraint. 
$
  
  [| x : alpha |] &= &&x space alpha \ 
  [| efun x -> e : alpha |] &= &&exists alpha_1 :: ty, alpha_2 :: ty.  &"fresh" alpha_1, alpha_2\ 
  &&&clet x = lambda alpha_3. alpha_3 = alpha_1 cin [| e : alpha_2 |]\ 
  &&&and alpha = alpha_1 -> alpha_2 \ 
  [| e_1 space e_2 : alpha |] &= &&exists alpha_1 :: ty, alpha_2 :: ty.  & "fresh" alpha_1, alpha_2 \ 
  &&& [| e_1 : alpha_1 |] and [| e_2 : alpha_2 |] \
  &&&and alpha_1 = alpha_2 -> alpha  \ 
  [| clet x = e_1 cin e_2 : alpha |] &= &&clet x = paren.l.double e_1 paren.r.double cin [| e_2 : alpha |] \ 
  [| efun (etype beta) -> e : alpha |] &= &&clet x = paren.l.double forall beta. e paren.r.double cin x <= alpha  &"fresh" x\ 
  [| (e : tau) : alpha |] &= &&alpha = ceil(tau) and exists beta :: ty. beta = ceil(tau) and [| e : beta |] &"fresh" beta\ 
  [| erefl : alpha |] &= &&exists beta :: ty. alpha = (beta = beta) &"fresh" beta \ 
  [| () : alpha |] &= &&exists scopev :: scope. alpha = [scopev]tunit &"fresh" scopev\
  [| ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : alpha |] &= &&exists beta :: ty. [| (e_1 : tau_1 = tau_2 ) : beta |] &"fresh" beta, eqname \ 
  &&& and eqname : tau_1 = tau_2 ==> [| e_2 : alpha |] \
  paren.l.double e paren.r.double &= &&lambda alpha. [| e : alpha |] &"fresh" alpha\ 
  paren.l.double forall alpha. e paren.r.double &= &&forall alpha :: ty. lambda beta . [| e : beta |] &"fresh" beta 
$

== Metatheory <constraint-gen-meta>

We wish to formalise a relationship between well-typed terms and satisfiable generated constraints obtained from them. So far, we have motiviated constraint generation as a constraint that is satisfiable if and only if the term is well-typed. 

_Assignment Extension._ To precisely state the metatheoretic property of soundness and completeness of constraint generation, we need to relate the typing context $Gamma$ to the assignment $Psi$ that satisfies the generated constraint. Informally, we can view the assignment as a "more solved" typing context. 

We capture this intuition using the _assignment extension_ judgement $Phi --> Phi'$. This judgement captures that $Phi'$ is "more solved" than $Phi$ by introducing new existential variables or solutions. Contexts $Gamma$ correspond to the _initial_ assignment from which the satisfiable assignment $Psi$ is extended from. 

The judgement $Phi --> Phi'$ is read _$Phi$ is extended by $Phi'$_ (or $Phi'$ extends $Phi$). The rules deriving the assignment extension judgement (Figure ??)
say that the empty assignment extends the empty assignment ($-->$Emp); polymorphic type variables must match ($-->$TyVar); equations must match ($-->$Eq); a term variable binding $x : sigma_2$ extends $x : sigma_1$ if applying the extending assignment $Phi_2$ to $sigma_1$ and $sigma_2$ yields the same type scheme ($-->$Var); and, existential (flexible type) variables may:
- appear in both assignments, if applying the extending assignment $Phi_2$ makes the solutions $tau_1^kappa$ and $tau_2^kappa$ equal ($-->$Solved),
- get solved by the extending assignment ($-->$Solve), rigid variables cannot be 'solved' -- they must remain polymorphic,
- be added by the extending assignment with a solution ($-->$NewSolved);

Extension is preserves several important properties. First, if a declaration appears in $Phi$, it must appear in all extensions of $Phi$. Second, extension preserves order (and thus well-formedness). And finally, extension cannot _remove_ solutions, it can only modify them, and only in a manner that preserves equality of the solution in the extending assignment.  

#judgement-box($Phi --> Phi'$)

$
  
  #proof-tree(
    rule(
      $dot --> dot$,
      $$, 
      name: [$-->$Emp]
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Phi_1, alpha ::^phi kappa --> Phi_2, alpha ::^phi kappa$, 
      $Phi_1 --> Phi_2$, 
      name: [$-->$TyVar]
    )
  )

  #v2


  #proof-tree(
    rule(
      $Phi_1, eqname : tau_1 = tau_2 --> Phi_2, eqname : tau_1 = tau_2$, 
      $Phi_1 --> Phi_2$, 
      name: [$-->$Eq]
    )
  )

  #h1 


  #proof-tree(
    rule(
      $Phi_1, x : sigma_1 --> Phi_2, x : sigma_2$, 
      $Phi_1 --> Phi_2$, 
      ${Phi_2}sigma_1 = {Phi_2}sigma_2$, 
      name: [$-->$Var]
    )
  )

  #v2 

  #proof-tree(
    rule(
      $Phi_1, alpha ::^fflex kappa := tau^kappa_1 --> Phi_2, alpha ::^fflex kappa := tau^kappa_2$, 
      $Phi_1 --> Phi_2$, 
      ${Phi}tau^kappa_1 = {Phi}tau^kappa_2$, 
      name: [$-->$Solved]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Phi_1, alpha ::^fflex kappa --> Phi_2, alpha ::^fflex kappa := tau^kappa$,
      $Phi_1 --> Phi_2$, 
      $Phi_2 tack tau^kappa :: kappa$, 
      name: [$-->$Solve]
    )
  )


  #v2 

  #proof-tree(
    rule(
      $Phi_1 --> Phi_2, alpha ::^fflex kappa := tau^kappa$,
      $Phi_1 --> Phi_2$, 
      $alpha disjoint Phi'$,
      $Phi_2 tack tau :: kappa$, 
      name: [$-->$NewSolved]
    )
  )
$

With the relation between typing contexts and assignments defined, we can succinctly state soundness and completeness of constraint generation with respect to #aml's typing judgements. 

#theorem[_Constraint generation is sound and complete with respect to #aml _][
  Given $Gamma ok$, $Gamma --> Phi$, and $Phi$ is the identity on $fv(e)$.  

  Then, $Phi tack [| e : alpha |]$ if and only if $Gamma tack e : {Phi}alpha$. 
]

The property is proved by structural induction on $e$; proof details are provided in the appendix. 




// _Equivalences_. Our later technical developments will rely on establishing equivalences between constraints, so we now define notions of _entailment_ and _equivalence_. 
// A constraint $C_1$ entails $C_2$, written $C_1 tack.double C_2$, if every context that satisfies $C_1$ also satisfies $C_2$. Similarly, equivalence $C_1 equiv C_2$ holds if the property is bidirectional.
