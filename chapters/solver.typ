#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

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