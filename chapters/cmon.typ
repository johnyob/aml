#import "../lib/syntax.typ": *

// System names
#let aml = textsf("AML")
#let ml = textsf("ML")

// Types
#let tint = textsf("int")
#let tstring = textsf("string")

#let tformer = textsf("F")
#let tforall(alpha) = $forall #alpha. space$
#let tforallb(alpha, bound) = $forall (#alpha >= #bound). space$

// Expressions
#let erefl = textsf("Refl")
#let elet = textsf("let")
#let ein = textsf("in")
#let ematch = textsf("match")
#let ewith = textsf("with")
#let efun = textsf("fun")
#let etype = textsf("type")

// Constraints
#let cdef = textsf("def")
#let cin = textsf("in")
#let ctrue = textsf("true")
#let cfalse = textsf("false")
#let clet = textsf("let")
#let cis = textsf("is")
#let cforall(alphas, C, gamma) = $forall #alphas . space #C => #gamma$

// Judgements
#let ok = textsf("ok")

// Functions
#let fv = textsf("fv")
#let arity = textsf("arity")