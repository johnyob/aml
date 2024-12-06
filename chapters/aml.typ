#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree

// HACK to get thm to left align
#show: thmrules

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

#let tformer = textsf("F")
#let tint = textsf("int")
#let ok = textsf("ok")

_Types_. The syntax of types is as follows:
#syntax(
  horizontal-spacing: 3cm,
  syntax-rule(name: [Type Variables], $alpha, beta, gamma$),
  syntax-rule(name: [Type Constructors], $tformer ::= dot arrow dot | tint | dot = dot | ...$),
  syntax-rule(name: [Types], $tau ::= alpha | overline(tau) tformer$),
  syntax-rule(name: [Shallow Types], $rho ::= alpha | overline(alpha) tformer$),
  syntax-rule(name: [Ambivalent Types], $psi ::= rho | psi approx alpha$),
  syntax-rule(name: [Ambivalent Bound], $psi_epsilon ::= psi | epsilon$),
  syntax-rule(name: [Type Schemes], $sigma ::= alpha | tforallb(alpha, psi_epsilon) sigma$),
  syntax-rule(name: [Contexts], $Gamma ::= &dot | Gamma, alpha >= psi_epsilon | Gamma, tau = tau | Gamma, x: sigma$),
)

// Types 
Types consist of type variables ($alpha$) and type constructors ($tformer$). Type constructors include functions ($arrow$), base types (such as $tint$), and the equality withness type ($=$). 

// Ambivalent types
Intuiviely, ambivalent types are a set of (provably equivalent) types. We use $approx$ to separate the elements in an ambivalent type: the operator is idempotent, associative, and commutative.
However, the syntax of ambivalent types is doesn't immediately correspond to the intuition. The reason behind this is to address the following challenge: when inferring types, we wish to track information such as the usage of type-level equalities. This information must be _shared_ across all uses of a type to correctly detect ambivalence when exiting the scope of a local constraint introduced by a $ematch$. We represent this explicit sharing of types using type variables ($alpha$). A context $Gamma$ can contain the 'structure' of the type ($alpha >= psi_epsilon in Gamma$).

// Schemes
_Type schemes_ are also affected by the notion of _sharing_. Instead of a normal quantifier ($tforall(alpha) sigma$), we introduce a _flexible bounded quantifier_ ($alpha >= psi_epsilon$). This is because on instantiation, _any_ type can be made ambivalent (provided it is consistent in the context), thus the type $psi$ represents a _lower bound_. We write $tforall(alpha) sigma$ for $tforallb(alpha, epsilon) sigma$.

// Contexts
Contexts bind program variables to type schemes, introduce _variable bounds_, and store type equations $tau = tau'$.
They are ordered and duplicates are disallowed. We write $Gamma, Gamma'$ for the concatenation of two contexts (assuming disjointness holds). 


#let fv = textsf("fv")

The definition for the set of free variables on types, shallow types, ambivalent types, and schemes is mostly standard.

#{
set align(center)
grid(
  columns: (auto, auto), 
  column-gutter: 3cm,
  row-gutter: 1cm,
  $
    fv_tau (alpha) &= { alpha } \ 
    fv_tau (overline(tau) tformer) &= union.big_i fv(tau_i) \
    #v1
    fv_psi (rho) &= fv_rho (rho) \ 
    fv_psi (psi approx alpha) &= fv_psi (psi) union { alpha } \ 
    #v1 
    fv_(psi_epsilon) (epsilon) &= emptyset \
  $, 
  $
    fv_rho (alpha) &= { alpha } \ 
    fv_rho (overline(alpha) tformer) &= { overline(alpha) } \ 
    #v1
    fv_sigma (alpha) &= { alpha } \ 
    fv_sigma (tforallb(alpha, psi_epsilon) sigma) &= fv(sigma) \\ {alpha} union fv_(psi_epsilon)(psi_epsilon) \ \
    #v1
    fv_(psi_epsilon) (psi) &= fv_psi (psi) 
  $
)
}

_Well formedness_. Well-formedness judgements for types, type schemes, and contexts ensure the soundness of ambivalent types and the coherent use of variables. We assume standard well-formedness judgement for types $Gamma tack tau ok$, which state that only type variables in $Gamma$ can appear in $tau$. 

#judgement-box($Gamma tack rho ok$, $Gamma tack psi ok$, $Gamma tack psi_epsilon ok$, $Gamma tack sigma ok$)

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

  #h1

  #proof-tree(
    rule(
      $Gamma scripts(tack)_psi rho ok$, 
      $Gamma tack rho ok$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack psi approx alpha ok$,
      $Gamma tack psi ok$,
      $Gamma tack alpha = psi$
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
      $Gamma scripts(tack)_(psi_epsilon) psi ok$, 
      $Gamma tack psi ok$
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma scripts(tack)_sigma alpha ok$, 
      $alpha in dom(Gamma)$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack tforallb(alpha, psi_epsilon) sigma$,
      $Gamma, alpha >= psi tack sigma ok$,
      $Gamma tack psi_epsilon ok$,
      $alpha \# Gamma$
    )
  )
$
We prove equivalence on _deep ambivalent types_. A deep ambivalent type is formally defined as:
$
  delta ::= alpha | overline(delta) tformer | delta approx delta
$
The set of (shallow) ambivalent types is a strict subset of deep ambivalent types. 

#comment([TODO: Explain why introduce deep ambivalent types? tl;dr: makes rules slightly nicer for proving consistency of shallow ambivalent types])


#judgement-box($Gamma tack delta_1 = delta_2$)


$
  #proof-tree(
    rule(
      $Gamma tack delta = delta$,
      $Gamma tack delta ok$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack delta_1 = delta_2$,
      $Gamma tack delta_2 = delta_1$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack delta_1 = delta_3$,
      $Gamma tack delta_1 = delta_2$,
      $Gamma tack delta_2 = delta_3$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack tau_1 = tau_2$,
      $tau_1 = tau_2 in Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack overline(delta_1) tformer = overline(delta_2) tformer$,
      $forall i. space Gamma tack delta_(1i)  = delta_(2i)$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack delta_(1i) = delta_(2i)$,
      $Gamma tack overline(delta_1) tformer = overline(delta_2) tformer$
    )
  )

  \

  #proof-tree(
    rule(
      $Gamma tack delta_1 approx delta_2 = delta_1$,
      $Gamma tack delta_1 = delta_2$,
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack delta_1 approx delta_2 = delta_2$,
      $Gamma tack delta_1 = delta_2$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack alpha = psi$, 
      $alpha >= psi in Gamma$
    )
  )

$

To prove such equivalences, we can either use equalities introduced previously in $Gamma$, and the rules of symmetry, transitivity, congruence, decomposition, and distributivity. Type constructors are injective.

#judgement-box($Gamma ok$)

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
      $Gamma, alpha >= psi_epsilon ok$,
      $Gamma ok$,
      $Gamma tack psi_epsilon ok$,
      $alpha \# Gamma$
    )
  )

  #v2

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





_Typing Judgements_. #aml typing judgements have the form $Gamma tack.r e: sigma$ stating that $e$ has the type (scheme) $sigma$ in the context $Gamma$. For the translation of types $tau$ into _shallow types_ used in the typing rules, we require the notion of _split types_. A split type $sigma.alt$ is a pair $Delta triangle.r.small alpha$, where $alpha$ encodes the type $tau$ in the (split type) context $Delta$. 
The translation of types to split types, denoted $floor(tau)$ is defined by:

$
  floor(alpha) &= beta >= alpha triangle.r.small beta #h(4cm) &&"fresh" beta\
  floor(overline(tau) tformer) &= Delta_1, dots, Delta_n, beta >= overline(alpha) tformer triangle.r.small beta &&"fresh" beta \ 
  &&&"where" floor(tau_i) = Delta_i triangle.r.small alpha_i
$
where $Delta ::= dot | Delta, alpha >= psi_epsilon$. We write $forall floor(tau)$ for the type scheme $forall Delta. alpha$. 


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
      $Gamma tack efun x -> e : tforallb(alpha, beta_1 -> beta_2) alpha$,
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
      $Gamma tack e : tforallb(alpha, psi_epsilon) sigma$,
      $Gamma, alpha >= psi_epsilon tack e : sigma$,
      $Gamma tack psi_epsilon ok$,
      $alpha\#Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack e : alpha$,
      $Gamma, beta >= psi_epsilon tack e : alpha$,
      $Gamma tack psi_epsilon ok$,
      $alpha eq.not beta$, 
      $beta \# Gamma$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack efun (etype alpha) -> e : tforall(alpha) sigma$,
      $Gamma, alpha tack e : sigma$,
      $alpha \# Gamma$
    )
  )

  #v2

  #proof-tree(
    rule(
      $Gamma tack (\_ : tau) : forall floor(tau -> tau)$,
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
      $Gamma tack erefl : tforall((alpha, beta >= alpha = alpha)) beta$,
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


#judgement-box($Gamma tack psi_epsilon <= psi_epsilon^'$, $Gamma tack psi_epsilon <= alpha$, $Gamma tack sigma <= sigma'$)



$
  #proof-tree(
    rule(
      $Gamma tack epsilon <= psi_epsilon$,
      $$
    )
  )
  #h1 

  #proof-tree(
    rule(
      $Gamma tack psi approx alpha <= psi' approx alpha$,
      $Gamma tack psi <= psi'$
    )
  )

  #h1

  #proof-tree(
    rule(
      $Gamma tack rho <= psi$,
      $rho in psi$
    )
  )
  #v2

  #proof-tree(
    rule(
      $Gamma tack alpha <= alpha$,
      $$
    )
  )

  #h1 

  #proof-tree(
    rule(
      $Gamma tack psi_epsilon <= alpha$,
      $Gamma tack psi_epsilon <= psi_epsilon^'$,
      $alpha >= psi_epsilon^' in Gamma$
    )
  )


  #v2

  #proof-tree(
    rule(
      $Gamma scripts(tack)_sigma alpha <= alpha$,
      $alpha in dom(Gamma)$
    )
  )


  #h1

  #proof-tree(
    rule(
      $Gamma tack tforallb(alpha, psi_epsilon) sigma <= sigma'$,
      $Gamma tack sigma[alpha := beta] <= sigma'$,
      $Gamma tack psi_epsilon <= beta$
    )
  )
$

_Examples_ of annotation types.
$
  floor(tint) & "is" &
  & beta >= tint triangle.r.small beta
  \
  forall floor(tint -> tint) & "is" &
  & tforall((beta_1 >= tint, beta_2 >= tint)) beta_1 -> beta_2
  \
  floor(alpha -> tint) & "is" &
  & beta >= alpha, gamma >= tint, delta >= beta -> gamma triangle.r.small delta
  \
  forall floor((alpha -> tint) -> (alpha -> tint)) & "is" &
  & tforall(lr((
     #block[$
     beta_1 >= alpha, gamma_1 >= tint, delta_1 >= beta_1 -> gamma_1, \
     beta_2 >= alpha, gamma_2 >= tint, delta_2 >= beta_2 -> gamma_2, \ 
     eta >= delta_1 -> delta_2
     $]
   ))) eta
$

_Examples_ of subsumption.
With $Delta = beta'_1 >= tint approx alpha, gamma'_1 >= tint approx alpha, delta'_1 >= beta'_1 -> gamma'_1, beta'_2 >= alpha, gamma'_2 >= tint, delta'_2 >= beta'_2 -> gamma'_2, eta' >= delta'_1 -> delta'_2$
$
  
  #proof-tree(
    rule(
      $underbrace(alpha\, alpha = tint\, Delta', Gamma) tack forall floor((alpha -> tint) -> (alpha -> tint)) <= eta$, 
      rule(
        $Gamma tack forall ( gamma_1 >= tint, ...). eta$,
        rule(
          $Gamma tack forall (delta_1 >= beta'_1 -> gamma'_1, ...). eta$, 
          
          rule($Gamma tack forall(beta_1 >= alpha, ...). eta$, $dots.v$), 
          rule(
            $Gamma tack beta'_1 -> gamma'_1 <= delta'_1$, 
            $dots.v$
          )
        ), 
        rule(
          $Gamma tack tint <= gamma'_1$,
          rule($Gamma tack tint <= tint approx alpha$, $dots.v$), 
          $gamma'_1 >= tint approx alpha in Gamma$
        )
      ), 
      rule(
        $Gamma tack alpha <= beta'_1$, 
        rule($Gamma tack alpha <= tint approx alpha$, $dots.v$),
        $beta'_1 >= tint approx alpha in Gamma$
      )
    )
  )
$

The above instantiation would be utilised in the following code example:
$
  elet "foo" = &efun (etype alpha) med (w : alpha = tint) -> \
  &ematch (w : alpha = tint) ewith erefl -> \ 
  & ((efun (x : alpha) -> x) : alpha -> tint)
$
where $efun (x : tau) -> e$ is syntactic sugar for $efun x -> elet x = (x : tau) ein e$. 
The function $efun (x : alpha) -> x$ would have the type 
$alpha -> alpha approx tint$ (sharing removed for readability). 

#comment[TODO: Do example with ambivalent coerce instantiation]. 



_Coherence_. An ambivalent type must be _coherent_, namely all the types in the ambivalent type are provably equal under the equations available in the context $Gamma$.

#definition[An ambivalent type $psi$ is said to be coherent in the context $Gamma$ if and only if $Gamma tack psi ok$]

Substitutions can operate on ambivalent types, allowing the instantiation of types such as $forall beta >= alpha approx tint. beta$. Substitutions therefore must preserve _coherence_. As a result of this, substitutions allow replacement of an ambivalent type by a "more ambivalent" one. Since the structure of types exists in the context, it is sufficient for substitutions to only substitute variables. 

#definition[A variable substitution $theta$ preserves ambivalence between $Delta$ and $Delta'$, written $theta : Delta => Delta' ok$, if and only if: \
  #{
    set enum(numbering: "(i)")
    text[
      + For all $alpha in dom(Delta)$, $theta(alpha) in dom(Delta')$ \
      + If $alpha >= psi_epsilon in Delta$, then $theta(alpha) >= psi'_epsilon in Delta'$ such that $psi_epsilon subset.eq psi'_epsilon$
    ]
  }]

#aml's typing judgements must also preserve coherence. This is ensured with the following regularity theorem:
#theorem("Regularity")[
  - If $Gamma ok$ and $Gamma tack delta_1 = delta_2$, then $Gamma tack delta_1 ok$ and $Gamma tack delta_2 ok$
  - If $Gamma ok$ and $Gamma tack e : sigma$, then $Gamma tack sigma ok$
]
#proof[
  #comment[TODO]
]


#comment[TODO: Principality & Monotonicity & Substitution Stability]

_Syntax-directed Typing Judgements._ #aml's typing judgements
are not syntax-directed. It is useful to have a syntax-directed presentation to admit inversion rules solely on the structure of $e$. 

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
      $Gamma tack e scripts(:)_sigma alpha$,
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
      $Gamma tack forall floor(tau -> tau) <= alpha$
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

#theorem[
  If $Gamma tack e : alpha$, then $Gamma scripts(tack)_"SD" e : alpha$

  #proof[
    
  ]
]


== Bracket Types

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

