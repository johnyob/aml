
#import "../lib/std.typ": *
#import "../lib/syntax.typ": *
#import "../lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree


#let cdef = textsf("def")
#let cin = textsf("in")
#let ctrue = textsf("true")
#let cfalse = textsf("false")
#let clet = textsf("let")
#let cis = textsf("is")

#let var = textsf("Var")
#let tformer = textsf("F")

#let gt = math.upright(math.bold("t"))
#let gz = math.upright(math.bold("z"))
#let gs = math.upright(math.bold("s"))

#comment([This section describes Olivier's semantics (with some minor syntactic changes)])

The syntax of constraints is as follows

#syntax(
  syntax-rule(name: [Constraint], $C ::= &ctrue | cfalse | C and C \ 
  | &exists zeta. C | forall alpha. C \ 
  | &zeta = zeta | psi cis zeta | A ==> C \  
  | &cdef x : sigma cin C | x <= zeta | sigma <= zeta \ 
  | &clet x : sigma cin C 
  $),

  syntax-rule(name: [Shallow Types], $psi ::= alpha | overline(zeta) tformer$), 

  syntax-rule(name: [Constrainted\ Type Scheme], $sigma ::= forall overline(alpha), overline(zeta). C => zeta $), 

  syntax-rule(name: [Assumptions], $A ::= ctrue | A and A | tau = tau$),

  syntax-rule(name: [Equational\ Contexts], $E ::= dot | E, gt = gt$),
  
  syntax-rule(name: [Assignment], $phi ::= dot | phi[alpha |-> gt] | phi[zeta |-> gz]$), 

  syntax-rule(name: [Environment], $rho ::= dot | rho[x |-> gs]$), 

  syntax-rule(name: [Context], $Delta ::= dot | Delta, alpha | Delta, zeta | Delta, x$)
)


Ground types are $gt$ and ground ambivalent types are $gz$. 

#judgement-box($E, phi, rho tack.r C $)
$
  #proof-tree(
    rule(
      $E, phi, rho tack.r ctrue$, 
      "",
      name: [(True)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $E, phi, rho tack.r C_1 and C_2$,
      $E, phi, rho tack.r C_1$,
      $E, phi, rho tack.r C_2$,
      name: [(Conj)]
    )
  )

  \

  #v(2cm)

  #proof-tree(
    rule(
      $E, phi, rho tack.r exists zeta. C$, 
      $E tack.r gz $, 
      $E, phi[zeta |-> gz], rho tack.r C$,
      name: [(Exists)]
    )
  )

  #h(1cm)


  #proof-tree(
    rule(
      $E, phi, rho tack.r forall alpha. C$, 
      $forall gt$, 
      $E, phi[alpha |-> gt], rho tack.r C$, 
      name: [(Forall)]
    )
  )
  
  \ 

  #v(2cm)

  #proof-tree(
    rule(
      $E, phi, rho tack.r zeta_1 = zeta_2$,
      $phi(zeta_1) = phi(zeta_2)$, 
      name: [(Equal)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $E, phi, rho tack.r psi cis zeta$,
      $phi(psi) cis phi(zeta)$, 
      name: [(Is)]
    )
  )

  \ 

  #v(2cm)

  #proof-tree(
    rule(
      $E, phi, rho tack.r A ==> C$, 
      $(E, phi(A)), phi, rho tack.r C$, 
      name: [(Impl)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $E, phi, rho tack cdef x : sigma cin C$, 
      $E, phi, rho[x |-> (E, phi, rho) sigma] tack C$, 
      name: [(Def)]
    )
  )

  \ 
  #v(2cm)

  #proof-tree(
    rule(
      $E, phi, rho tack x <= zeta$, 
      $phi(zeta) in rho(x)$, 
      name: [(VarInst)]
    )
  )


  #h(1cm)

  #proof-tree(
    rule(
      $E, phi, rho tack sigma <= zeta$, 
      $phi(zeta) in (E, phi, rho) sigma$, 
      name: [(SchemeInst)]
    )
  )

$

$
  #proof-tree(
    rule(
      $E, phi, rho tack clet x : sigma cin C$, 
      $E, phi, rho tack exists sigma$, 
      $E, phi, rho[x |-> (E, phi, rho) sigma] tack C$, 
      name: [(Let)]
    )
  ) 

  \ 

  #v(2cm)

  (E, phi, rho) (forall overline(alpha), overline(zeta). C => zeta) eq.delta { phi'(zeta) : phi scripts(=)_(\\ overline(alpha), overline(zeta)) phi' and E, phi', rho tack C} \ 

  #proof-tree(
    rule(
      $E, phi, rho tack exists (forall overline(alpha), overline(zeta). C => zeta)$, 
      $E, phi, rho tack forall overline(alpha). exists overline(zeta). C$
    )
  )
$

#let ok = textsf("ok")

#judgement-box($Delta tack.r C ok$)

$
  #proof-tree(
    rule(
      $Delta tack.r ctrue ok$, 
      $$,
      name: [(True)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $Delta tack.r cfalse ok$, 
      $$,
      name: [(False)]
    )
  )

  \ 

  #v(2cm) 

  #proof-tree(
    rule(
      $Delta tack.r C_1 and C_2 ok$,
      $Delta tack.r C_1 ok$, 
      $Delta tack.r C_2 ok$, 
      name: [(Conj)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $Delta tack.r exists zeta. C ok$, 
      $Delta, zeta tack C ok$, 
      $zeta \# Delta$,
      name: [(Exists)]
    )
  )

  \

  #v(2cm)

  #proof-tree(
    rule(
      $Delta tack.r forall alpha. C ok$, 
      $Delta, alpha tack.r C ok$, 
      $alpha \# Delta$,
      name: [(Forall)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $Delta tack zeta_1 = zeta_2 ok$, 
      $zeta_1, zeta_2 in Delta$, 
      name: [(Equal)]
    )
  )

  \

  #v(2cm)

  #proof-tree(
    rule(
      $Delta tack psi cis zeta ok$, 
      $Delta tack psi ok$, 
      $zeta in Delta$, 
      name: [(Is)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $Delta tack A ==> C ok$, 
      $Theta tack A ok$, 
      $Delta tack C ok$, 
      name: [(Impl)]
    )
  )

  \ 

  #v(2cm)

  #proof-tree(
    rule(
      $Delta tack cdef x : sigma cin C ok$, 
      $Theta tack sigma ok$,
      $Delta, x tack C ok$,
      $x \# Delta$, 
      name: [(Def)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $Delta tack x <= zeta ok$, 
      $x in Delta$, 
      $zeta in Theta$, 
      name: [(VarInst)]
    )
  )

  \ 

  #v(2cm)

  #proof-tree(
    rule(
      $Delta tack sigma <= zeta ok$, 
      $Delta tack sigma ok$,
      $zeta in Theta$, 
      name: [(SchemeInst)]
    )
  )

  #h(1cm)

  #proof-tree(
    rule(
      $Delta tack clet x : sigma cin C ok $, 
      $Delta tack sigma ok$, 
      $Delta, x tack C ok$,
      $x \# Delta$, 
      name: [(Let)]
    )
  ) 


  \ 

  #v(2cm)

  #proof-tree(
    rule(
      $Delta tack forall overline(alpha), overline(zeta). C => zeta ok$, 
      $Theta'; Delta tack C ok$, 
      $zeta in Theta'$, 
      $overline(alpha), overline(zeta) \# Theta$, 
      name: [(Scheme)], 
      label: $Theta' = Theta, overline(alpha), overline(zeta)$
    )
  )
  
$

#pagebreak()

== Constraint Generation

We introduce a function $[| e : zeta |]$, which translates the expression $e$ and type variable $zeta$ to a constraint. Assuming $e$ is well-formed under $Delta$ ($Theta; Delta tack e ok $), then $[| e : zeta |]$ is well-formed under $Theta; Delta$ and $zeta$ ($Theta, zeta; Delta tack [|e : zeta|] ok$). 


#let erefl = textsf("Refl")
#let elet = textsf("let")
#let ein = textsf("in")
#let ematch = textsf("match")
#let ewith = textsf("with")
#let efun = textsf("fun")
#let etype = textsf("type")
#let eabsurd = textsf("absurd")
#let tformer = textsf("F")

$
  
  [| x : zeta |] &= x <= zeta \ 
  [| efun x -> e : zeta |] &= exists zeta_1 zeta_2. cdef x: zeta_1 cin [| e : zeta_2 |] and zeta_1 -> zeta_2 cis zeta \ 
  [| e_1 e_2 : zeta |] &= exists zeta_1, zeta_2. [| e_1 : zeta_1 |] and [| e_2 : zeta_2 |] and zeta_2 -> zeta cis zeta_1 \ 
  [| clet x = e_1 cin e_2 : zeta |] &= clet x : paren.l.double e_1 paren.r.double cin [| e_2 : zeta |] \ 
  [| efun (etype alpha) -> e : zeta |] &= clet x : paren.l.double e paren.r.double_alpha cin x <= zeta \ 
  [| (e : tau) : zeta |] &= tau cis zeta and [| e : tau |] \ 
  [| erefl : zeta |] &= exists zeta'. zeta' = zeta' cis zeta \ 
  // [| eabsurd : zeta |] &= eabsurd \ 
  [| ematch (e_1 : tau_1 = tau_2) ewith erefl -> e_2 : zeta |] &= [| e_1 : tau_1 = tau_2 |] and (tau_1 = tau_2) ==> [| e_2 : zeta |]
$

$
  paren.l.double e paren.r.double &= forall zeta. [| e : zeta |] => zeta \ 
  paren.l.double e paren.r.double_alpha &= forall alpha, zeta. [| e : zeta |] => zeta 

$

_Split Types_. For the translation of types $tau$ into shallow types used in constraints, we require the notion of split types. Split types $sigma.alt$  are a pair $Xi triangle.small.r zeta$, where the (deep) type may be reconstructed from the subset constraints in $Xi$ and variable $zeta$.
More formally, the grammar of split types $sigma.alt$ is given by:
$
  sigma.alt ::= Xi triangle.small.r zeta #h(1cm) Xi ::= exists overline(zeta). Omega #h(1cm) Omega ::= dot | Omega, zeta supset.eq psi
$
where $psi$ is an shallow type. Here is formal translations between split and deep types:
$
  ceil(alpha) &= exists zeta. zeta supset.eq alpha triangle.small.r zeta \ 
  ceil(zeta) &= dot triangle.small.r zeta \ 
  ceil(overline(tau) tformer) &= exists zeta. overline(Xi), zeta supset.eq overline(zeta) tformer triangle.small.r zeta &#h(2cm) &"where" ceil(tau_i) = Xi_i triangle.small.r zeta_i \ 
$
We can now extend the constraint language with the subset constraint $tau cis zeta$ using split types, defined by:
$
  tau cis zeta eq.delta exists overline(zeta). and.big Omega and zeta' = zeta #h(2cm) "where" ceil(tau) = exists overline(zeta). Omega triangle.small.r zeta'
$
We can additional extend the constraint generation function $[| e : zeta |]$ to be defined on $[| e : tau |]$
$
  [| e : tau |] &= exists zeta. tau cis zeta and [| e : zeta |]
$

== Problems 


Substitutivity of rigid types

```ocaml
let coerce = 
  fun (type a b) -> fun w -> fun x -> 
  let w = (w: (a, b) eq) in 
  let x = (x: a) in
  match (w : (a, b) eq) with Refl -> (x : b)

let f =
  fun (type a) -> fun w -> fun x -> 
  let w = (w : (a, int) eq) in 
  let x = (x : a) in 
  match (w : (a, int) eq) with Refl -> 
      let y = if true then x else 1 in 
      ignore (coerce Refl y) 
```

Generated constraints:

$
  paren.double.l"coerce"paren.double.r_(alpha, beta) &= forall alpha, beta, zeta. \ 
    & exists zeta_w, zeta_x, zeta_r. zeta_w -> zeta_x -> zeta_r cis zeta and   cdef w: zeta_w, x: zeta_x cin \ 
    &clet w: forall zeta_w'. alpha = beta cis zeta_w' and w <= alpha = beta => zeta_w' cin \ 
    &clet x: forall zeta_x'. alpha cis zeta_x' and x <= alpha cin \ 
    &[| w : alpha = beta|] and alpha = beta ==> exists zeta_r'. beta cin zeta_r and beta cin zeta_r' and x <= zeta_r' \

    &=> zeta
$

Doing some solving, we get
$
 paren.double.l"coerce"paren.double.r_(alpha, beta) &= forall alpha, beta, zeta_w, zeta_x, zeta_r, zeta. \
 &#h1 zeta_w -> zeta_x -> zeta_r cis zeta \ 
 &#h1 and alpha = beta cin zeta_w and alpha cin zeta_x and beta cin zeta_r  => zeta
$

Ah ha! So this split means we don't propagate ambivalence correctly! Since if apply a value with $zeta = zeta$ for `w` where $zeta$ is ambivalent $alpha approx "int"$, then the return annotation $beta cin zeta_r$ doesn't ensure that the ambivalence is propagated. Something is wrong with our spec!

Now Olivier's rule for applying `coerce` does trace ambivalence, but it breaks substitution on implication constraints. 



Now looking at `f`:
$
  [| f : zeta |] &= 
    clet f_1 : forall alpha, zeta_1 . [| ... : zeta_1 |] => zeta_1 
    cin f_1 <= zeta \ 

  [| ... : zeta_1 |] &= exists zeta_w, zeta_x, zeta_r. 
  zeta_w -> zeta_x -> zeta_r cis zeta_1 \ 
  &and
  cdef w : zeta_w, x : zeta_x cin [| ... : zeta_r |] \ 

  [| ... : zeta_r|] &= clet w : forall zeta_w'. alpha = "int" cis zeta_w' and w <= alpha = "int" => zeta_w', \
  &#h1 x : forall zeta_x'. alpha cis zeta_x' => zeta_x' and x <= alpha => zeta_x' \
  &#h1 cin [| ... : zeta_r|]\
  [| ematch ... : zeta_r|] &= [| w : alpha = "int" |] and alpha = "int" ==> [| ... : zeta_r |] \ 
  [| clet y = ... : zeta_r|] &= clet y : forall zeta_y. x <= zeta_y and "int" cis zeta_y => zeta_y cin [| ... : zeta_r |] \ 
  [| "ignore" ... : zeta_r |] &= "unit" cis zeta_r and exists zeta'. [| "coerce" erefl y : zeta' |] 
$



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