#import "../lib/syntax.typ": *

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
#let InfCtx = textsf("InfCtx")
#let Exp = textsf("Exp")
#let Con = textsf("Con")
#let EqName = textsf("EqName")
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


#let fflex = $upright(f)$
#let frigid = $upright(r)$

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
#let rigid = textsf("rigid")

// Functions
#let fv = textsf("fv")
#let arity = textsf("arity")
#let consistent = textsf("consistent")
#let dangerous = $textsf("dangerous")$