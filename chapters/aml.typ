#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree

#let aml = textsf("AML")
#let ml = textsf("ML")


In this section we summarise the syntax and typing rules of #aml (Ambivalent ML), a conservative extension of the #ml calculus with _ambivalent types_ ($tau approx tau'$) and a type-level equality type ($tau = tau'$).

#let tint = textsf("tint")
#let erefl = textsf("Refl")
#let elet = textsf("let")
#let ein = textsf("in")
#let ematch = textsf("match")
#let ewith = textsf("with")
#let efun = textsf("fun")
#let etype = textsf("type")
#let eabsurd = textsf("absurd")

_Expressions_. The syntax of expressions is as follows:
#syntax(
  syntax-rule(
    name: [Expressions],
    $e ::= &x | efun x -> e | e space e \
      | &elet x = e ein e | efun (etype alpha) -> e | (e : tau) \
      | &erefl | eabsurd | ematch (e : tau = tau) ewith erefl -> e$,
  ),
)

#aml extends #ml expressions, variables, functions and let expressions are standard. #aml introduces an explicit universal quantifier $efun (etype alpha) -> e$, equivalent to System #textsf("F")'s $Lambda alpha. e$. The constructor $erefl$ has the type $tau = tau$. The $ematch (e : tau_1 = tau_2) ewith erefl -> e'$ construct introduces the type-level equality in $e'$ as a _local constraint_ using the proof $e$. The $eabsurd$ term is used to refute statically impossible cases, such as a inconsistent local constraint $tint = textsf("string")$.

== Bracket Types

#let tformer = textsf("F")
#let tint = textsf("int")


_Types._ The syntax of types is as follows:
#syntax(
  horizontal-spacing: 3cm,
  syntax-rule(name: [Type Variables], $alpha, beta, gamma$),
  syntax-rule(name: [Type Constructors], $tformer ::= dot arrow dot | tint | dot = dot | ...$),
  syntax-rule(name: [Types], $tau ::= alpha | overline(tau) tformer | tau approx tau | angle.l tau angle.r$),
  syntax-rule(name: [Type Schemes], $sigma ::= tau | forall alpha. sigma$),
  syntax-rule(name: [Contexts], $Gamma ::= dot | Gamma, alpha | Gamma, tau = tau | Gamma, x : sigma$),
)

Types are assembled from type variables ($alpha$), type constructors ($tformer$), and _ambivalent types_ ($approx$). Type constructors include functions ($arrow$), base types (such as $tint$), and the equality witness type ($=$).
Intuitively, an ambivalent type represents two _equivalent_ types. We extend this notion to sets of types, where $approx$ is used separate the elements of the set: it is distributive, associative, commutative and idempotent.

$
  tau approx tau &equiv tau \
  tau_1 approx tau_2 &equiv tau_2 approx tau_1 \
  tau_1 approx (tau_2 approx tau_3) &equiv (tau_1 approx tau_2) approx tau_3 \
  (tau_1, ..., tau_2 approx tau_2^', ..., tau_n) tformer &equiv (tau_1, ..., tau_2, ..., tau_n) tformer approx (
    tau_1, ..., tau_2^', ..., tau_n
  ) tformer
$

We consider types equal modulo alpha-renaming and the above equalivance involving $approx$.

One of the brand-new features, unique to this presentation of #aml, is the "bracketed" monotypes $angle.l tau angle.r$.
The intuition is this: _the un-bracketed parts of a type can be traced to an annotation of a 'known' typing rule, whereas the bracketed parts cannot_. They address the following challenge. When inferring types, we wish to track known information such as the usage of type-level equations. This information must be _shared_ across all uses of the type $tau$. However, when instantiating any type can become _ambivalent_ using subsumption and the equations in the context. When a type is 'guessed' (bracketed), we do not permit this kind of subsumption.
Traditionally 'sharing' was used to solve this problem.

Polymorphic types are defined by _type schemes_ in a mostly typical #ml fashion, generalzing over zero or more variables. A type is said to be _simple_ if it doesn't contain any ambivalent or bracket types.


#let fv = textsf("fv")

The definition for the set of free variables, written $fv$, is mostly standard with the exception of ambivalent types and brackets.

$
  fv(alpha) &= { alpha } \
  fv(overline(tau) tformer) &= union.big_i fv(tau_i) \
  fv(tau_1 approx tau_2) &= fv(tau_1) union fv(tau_2) \
  fv(angle.l tau angle.r) &= fv(tau) \
  fv(forall alpha. sigma) &= fv(sigma) \\ {alpha}
$

We write $ceil(tau)$ to strip all brackets of $tau$ and $floor(tau)$ to "fully bracket" $tau$, defined as follows:
$
  ceil(alpha) &= alpha \
  ceil(overline(tau) tformer) &= overline(ceil(tau)) tformer \
  ceil(tau_1 approx tau_2) &= ceil(tau_1) approx ceil(tau_2) \
  ceil(angle.l tau angle.r) &= tau \ \
  floor(tau) &= angle.l ceil(tau) angle.r
$

We write $tau arrow.b$ to push brackets down one level:
$
  angle.l overline(tau) tformer angle.r arrow.b &= overline(angle.l tau angle.r) tformer \
  angle.l tau_1 approx tau_2 angle.r arrow.b &= angle.l tau_1 angle.r approx angle.l tau_2 angle.r \
  angle.l angle.l tau angle.r angle.r arrow.b &= angle.l tau angle.r arrow.b \
  tau arrow.b &= tau &"otherwise"
$


_Well-formedness Judgements._ Well-formedness judgements for types, type schemes, and contexts ensure the soundness of ambivalent types and the coherent use of variables.

#let ok = textsf("ok")

#judgement-box($Gamma tack tau ok$, $Gamma tack sigma ok$, $Gamma ok$)

$
  #proof-tree(
    rule(
      $Gamma tack alpha ok$,
      $Gamma ok$,
      $alpha in Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(tau) tformer ok $,
      $forall i.$,
      $Gamma tack tau_i ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_1 approx tau_2 ok$,
      $Gamma tack tau_1 = tau_2$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack tau ok$,
      $Gamma tack tau ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack forall alpha. sigma ok$,
      $Gamma, alpha tack sigma ok$,
      $alpha \# Gamma$,
    )
  )

  #v1

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
      $alpha \# Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, tau_1 = tau_2 ok$,
      $Gamma ok$,
      $Gamma tack tau_1 ok$,
      $Gamma tack tau_2 ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma, x : sigma ok$,
      $Gamma ok$,
      $Gamma tack sigma ok$,
      $x \# Gamma$
    )
  )
$

#judgement-box($Gamma tack tau_1 = tau_2$)

$
  #proof-tree(
    rule(
      $Gamma tack tau = tau$,
      $Gamma tack tau ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_1 = tau_2$,
      $Gamma tack tau_2 = tau_1$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_1 = tau_3$,
      $Gamma tack tau_1 = tau_2$,
      $Gamma tack tau_2 = tau_3$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack tau_1 = tau_2$,
      $Gamma ok$,
      $tau_1 = tau_2 in Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(tau_1) tformer = overline(tau_2) tformer$,
      $forall i. space Gamma tack tau_(1i)  = tau_(2i)$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_(1i) = tau_(2i)$,
      $Gamma tack overline(tau_1) tformer = overline(tau_2) tformer$
    )
  )

  \

  #proof-tree(
    rule(
      $Gamma tack tau_1 approx tau_2 = tau_1$,
      $Gamma tack tau_1 = tau_2$,
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_1 approx tau_2 = tau_2$,
      $Gamma tack tau_1 = tau_2$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack angle.l tau_1 angle.r = angle.l tau_2 angle.r$,
      $Gamma tack tau_1 = tau_2$
    )
  )
$

To prove such equivalences, we can either use equalities introduced previously in $Gamma$, and the rules of symmetry, transitivity, congruence, decomposition, and distributivity. Type constructors are injective.

_Normal forms._ The equivalence on ambivalent types gives rise to a _normal form_.

#let nf = textsf("nf")

$
  #proof-tree(
    rule(
      $alpha nf$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $overline(tau) tformer nf$,
      $forall i. space tau_i nf$
    )
  )

  #h1

  #proof-tree(
    rule(
      $tau approx alpha nf$,
      $tau nf$
    )
  )

  #h1

  #proof-tree(
    rule(
      $angle.l tau angle.r nf$,
      $tau nf$
    )
  )
$

This corresponds to the idea that ambivalence relies on equalities introduced by _rigid_ type variables $alpha$.

#comment([TODO: Prove that any type has a normal form and that the normal form is equivalent.])


_Typing Judgements._ #aml typing judgements have the form $Gamma tack.r e: sigma$ stating that $e$ has the type (scheme) $sigma$ in the context $Gamma$.
The typing rules are given below.

#let simp = textsf("simp")

#let ty = textsf("Ty")
#let option = textsf("Option")
#let osome = textsf("Some")
#let onone = textsf("None")


#judgement-box($Gamma tack.r e : sigma$)

$
  #proof-tree(
    rule(
      $Gamma tack.r x : Gamma(x)$,
      $$,
      name: [(Var)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack.r efun x -> e : angle.l tau_1 angle.r -> tau_2$,
      $Gamma, x : angle.l tau_1 angle.r tack e : tau_2$,
      $Gamma tack tau_1 ok$,
      name: [(Fun)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e : sigma'$,
      $Gamma tack e : sigma$,
      $Gamma tack sigma <= sigma'$,
      name: [(Sub)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack e : forall alpha. sigma$,
      $Gamma, alpha tack e : sigma$,
      $alpha \# Gamma$,
      name: [(Gen)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack.r e_1 space e_2 : tau_3$,
      $Gamma tack.r e_1 : tau_1$,
      $Gamma tack.r e_2 : tau_2$,
      $tau_1 circle tau_2 = osome tau_3$,
      name: [(App)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack.r elet x = e_1 ein e_2 : sigma_2$,
      $Gamma tack.r e_1 : sigma_1$,
      $Gamma, x: sigma_1 tack.r e_2 : sigma_2$,
      name: [(Let)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack.r efun (etype alpha) -> e : forall alpha. sigma$,
      $Gamma, alpha tack e : sigma$,
      $alpha \# Gamma$,
      name: [(TFun)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack (e : tau) : tau$,
      $Gamma tack e : sigma$,
      $Gamma tack tau <= sigma$,
      $tau simp$,
      name: [(Ann)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : forall alpha. alpha = alpha$,
      $$,
      name: [(Refl)]
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack eabsurd : sigma $,
      $Gamma tack overline(tau)_1 space tformer_1  = overline(tau)_2 space tformer_2$,
      $tformer_1 != tformer_2$,
      $Gamma tack sigma ok$,
      name: [(Bot)]
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : sigma$,
      $Gamma tack e_1 >= tau_1 = tau_2$,
      $Gamma, tau_1 = tau_2 tack e_2 : sigma$,
      $Gamma tack sigma ok$,
      name: [(Match)]
    )
  )
$


#judgement-box($Gamma tack tau_1 <= tau_2$, $Gamma tack sigma_1 <= sigma_2$)


$
  #proof-tree(
    rule(
      $Gamma tack tau <= tau$,
      $Gamma tack tau ok $
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tau_1 <= tau_3$,
      $Gamma tack tau_1 <= tau_2$,
      $Gamma tack tau_2 <= tau_3$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack tau <= floor(tau)$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(tau) tformer <= overline(tau') tformer$,
      $Gamma tack tau_i <= tau_i^'$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack tau_1 <= tau_2 approx alpha$,
      $Gamma tack alpha = tau_2$,
      $Gamma tack tau_1 <= tau_2$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack forall alpha. sigma <= sigma'$,
      $Gamma tack sigma [alpha := angle.l tau angle.r] ok$,
      $Gamma tack sigma[alpha := angle.l tau angle.r] <= sigma'$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack sigma <= forall beta. sigma'$,
      $Gamma, beta tack sigma <= sigma'$
    )
  )
$

The application rule uses the function $dot circle dot : ty times ty -> option(ty)$:
$
  tau_1 -> tau_2 circle tau &= cases(
    osome tau_2 #h1&"if" tau_1 = tau,
    onone &"otherwise"
  ) \
  overline(tau) tformer circle tau &= onone \
  alpha circle tau &= onone \
  tau_1 approx tau_2 circle tau &= (tau_1 circle tau) circle(approx) (tau_2 circle tau) \
  tau circle tau_1 approx tau_2 &= cases(
    osome tau_3 #h1&"if" tau circle tau_1 = osome tau_3 ,
    &#h(3mm)and tau circle tau_2 = osome tau_3,
    onone &"otherwise"
  ) \
  angle.l tau_1 angle.r circle tau_2 &= angle.l tau_1 angle.r arrow.b circle tau_2
$

where $circle(approx) : option(ty) times option(ty) -> option(ty)$ is given by:

$
  osome tau_1 &circle(approx) osome tau_2 &&= osome (tau_1 approx tau_2) \
  onone &circle(approx) osome tau &&= osome tau \
  osome tau &circle(approx) onone &&= osome tau \
  onone &circle(approx) onone &&= onone
$

#comment([TODO: Define and prove correspondence of types and judgements between the 'bracket' system and the explcitly shared system])

#pagebreak()

== Explcit Sharing

This section describes a variant of the system presented in Garrigue and Remy's work without _locally abstract types_.

_Types_. Syntax of types is as follows:
#syntax(
  horizontal-spacing: 3cm,
  syntax-rule(name: [Type Variables], $alpha, beta, gamma$),
  syntax-rule(name: [Type Constructors], $tformer ::= dot arrow dot | tint | dot = dot | ...$),
  syntax-rule(name: [Types], $tau ::= alpha | overline(tau) tformer$),
  syntax-rule(name: [Shallow Types], $rho ::= alpha | overline(alpha) tformer$),
  syntax-rule(name: [Ambivalent Types], $psi ::= epsilon.alt | rho | psi approx alpha$),
  syntax-rule(name: [Type Schemes], $sigma ::= alpha | forall (alpha >= psi). sigma$),
  syntax-rule(name: [Contexts], $Gamma ::= &dot | Gamma, alpha >= psi | Gamma, tau = tau | Gamma, x: sigma$),
)

_Well formedness_.

#judgement-box($Gamma tack rho ok$, $Gamma tack psi ok$, $Gamma tack sigma ok$)

$
  #proof-tree(
    rule(
      $Gamma tack alpha ok$,
      $alpha in dom(Gamma)$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(alpha) tformer ok$,
      $forall i. space alpha_i in dom(Gamma)$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack epsilon.alt ok$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack psi approx alpha ok$,
      $Gamma tack psi ok$,
      $Gamma tack alpha = Gamma(psi)$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack forall (alpha >= psi). sigma$,
      $Gamma, alpha >= psi tack sigma ok$,
      $Gamma tack psi ok$,
      $alpha \# Gamma$
    )
  )
$

Type equivalence $Gamma tack tau_1 = tau_2$ is a subset of the previous system.

We write $Gamma(psi)$ for applying $Gamma$ as a substitution to $psi$, creating a type $tau$ (from the previous system).

Well-formedness of contexts is identical to the previous system.

_Typing Judgements_.

#judgement-box($Gamma tack e : sigma$)

$
  #proof-tree(
    rule(
      $Gamma tack x : Gamma(x)$,
      $$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun x -> e : forall alpha >= beta_1 -> beta_2. alpha$,
      $Gamma, x : beta_1 tack e : beta_2$,
      $Gamma tack beta_1 ok$
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma tack e_1 space e_2 : beta_2$,
      $Gamma tack e_1 : alpha_1$,
      $Gamma tack e_2 : beta_1$,
      $Gamma tack beta_1 -> beta_2 <= alpha_1$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack e : forall (alpha >= psi). sigma$,
      $Gamma, alpha >= psi tack e : sigma$,
      $Gamma tack psi ok$,
      $alpha\#Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e : alpha$,
      $Gamma, beta >= psi tack e : alpha$,
      $Gamma tack psi ok$,
      $alpha eq.not beta \# Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun (etype alpha) -> e : forall alpha. sigma$,
      $Gamma, alpha tack e : sigma$,
      $alpha \# Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (\_ : tau) : forall ceil(tau -> tau)$,
      $Gamma tack tau ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : sigma_2$,
      $Gamma tack e_1 : sigma_1$,
      $Gamma, x: sigma_1 tack e_2 : sigma_2$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack erefl : forall alpha, beta >= alpha = alpha. beta$,
      $$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : beta$,
      $Gamma tack (e_1 : tau_1 = tau_2) : alpha$,
      $Gamma, tau_1 = tau_2 tack e_2 : beta$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack e : sigma'$,
      $Gamma tack e : sigma$,
      $Gamma tack sigma <= sigma'$,
    )
  )
$


#judgement-box($Gamma tack rho <= alpha$, $Gamma tack sigma_1 <= sigma_2$)


$
  #proof-tree(
    rule(
      $Gamma tack rho <= alpha$,
      $alpha >= psi in Gamma$,
      $rho in psi$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack alpha <= alpha$,
      $$
    )
  )


  #h1

  #proof-tree(
    rule(
      $Gamma tack forall alpha >= psi. sigma <= sigma'$,
      $Gamma tack sigma[alpha := beta] <= sigma'$,
      $beta >= psi' in Gamma$,
      $psi subset.eq psi'$
    )
  )
$

The translation of simple types to split view, denoted $ceil(tau)$ is defined by:


$
  ceil(alpha) &= beta >= alpha triangle.r.small beta #h(4cm) &&"fresh" beta\
  ceil(overline(tau) tformer) &= Delta_1 times dots times Delta_n, beta >= overline(alpha) tformer triangle.r.small beta &&"fresh" beta
$

We write $forall ceil(tau)$ for the converted type scheme.

_Syntax Directed._ Its useful to have a syntax-directed set of typing rules (for proving equivalence between constraint generation and typing).

#judgement-box($Gamma tack e : alpha$, $Gamma tack e : sigma$)

$
  #proof-tree(
    rule(
      $Gamma tack x : alpha$,
      $Gamma(x) = sigma$,
      $Gamma tack sigma <= alpha$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun x -> e : alpha$,
      $Gamma, x : beta_1 tack e : beta_2$,
      $Gamma tack forall gamma >= beta_1 -> beta_2. gamma <= alpha$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e_1 space e_2 : beta_2$,
      $Gamma tack e_1 : alpha_1$,
      $Gamma tack e_2 : beta_1$,
      $Gamma tack beta_1 -> beta_2 <= alpha_1$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack e : forall (alpha >= psi). sigma$,
      $Gamma, alpha >= psi tack e : sigma$,
      $Gamma tack psi ok$,
      $alpha\#Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e scripts(:)^sigma alpha$,
      $Gamma, beta >= psi tack e : alpha$,
      $Gamma tack psi ok$,
      $alpha eq.not beta$,
      $beta \# Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun (etype alpha) -> e : beta$,
      $Gamma, alpha tack e : sigma$,
      $Gamma tack forall alpha. sigma <= beta$,
      $alpha \# Gamma$,
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (\_ : tau) : alpha$,
      $Gamma tack tau ok$,
      $Gamma tack forall ceil(tau -> tau) <= alpha$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack elet x = e_1 ein e_2 : alpha$,
      $Gamma tack e_1 : sigma$,
      $Gamma, x: sigma tack e_2 : alpha$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack erefl : gamma$,
      $Gamma tack (forall alpha, beta >= alpha = alpha. beta) <= gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : beta$,
      $Gamma tack (e_1 : tau_1 = tau_2) : alpha$,
      $Gamma, tau_1 = tau_2 tack e_2 : beta$
    )
  )
$

#comment([TODO: prove equivalence between non-syntax directed rules and syntax directed rules])

