#import "../lib/syntax.typ": *

#let textsf = text.with(font: "roboto")

#let dom = textsf("dom")
#let rng = textsf("rng")

// System names
#let aml = textsf("AML")
#let ml = textsf("ML")
#let xaml = textsf("xAML")

// Sets
#let varset(s) = $cal(V)_(#s)$
#let disjoint = $op(\#)$

#let Ty = textsf("Ty")
#let TyCon = textsf("TyCon")
#let Scm = textsf("Scm")
#let Scope = textsf("Scope")
#let Ctx = textsf("Ctx")
#let Exp = textsf("Exp")
#let Con = textsf("Con")
#let ConAbs = textsf("ConAbs")
#let ConCtx = textsf("ConCtx")
#let EqName = textsf("EqName")
#let Assn = textsf("Assn")
#let Kind = textsf("Kind")
#let Flex = textsf("Flex")

#let ty = textsf("ty")
#let scope = textsf("sc")
#let GTy = textsf("GTy")
#let GInst = textsf("GInst")
#let GScm = textsf("GScm")

// Types
#let eqname = $phi.alt$
#let tint = textsf("int")
#let tstring = textsf("string")
#let tunit = textsf("unit")
#let tformer = textsf("F")
#let tformerg = textsf("G")
#let tforall(alpha) = $forall #alpha. space$
#let scopev = $sigma.alt$

// Flexibility
#let fflex = $upright(f)$
#let frigid = $upright(r)$
#let fbind(f) = $op(scripts(::)^#f)$

// Expressions / terms
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



#let gt = math.upright(math.bold("t"))
#let gs = math.upright(math.bold("s"))
#let gi = math.upright(math.bold("inst"))

// Judgements
#let ok = textsf("ok")
#let ctx = textsf("ctx")
#let assn = textsf("assn")
#let scm = textsf("scm")
#let rigid = textsf("rigid")

#let dangerous = $textsf("dangerous")$

#let sdtack = $scripts(tack)_textsf("SD")$

// Functions
#let fv = textsf("fv")
#let arity = textsf("arity")
#let consistent = textsf("consistent")
#let dangerous = $textsf("dangerous")$
