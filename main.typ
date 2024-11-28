#import "lib/template.typ": *

#show: cam-notes.with(
  title: [ Constraint-Based Type Inference for GADTs ],

  subtitle: [ Technical Report ],

  author: "Alistair O'Brien",

  college: [ Queens' College ],

  date: datetime.today()
    .display("[month repr:long] [day padding:none], [year repr:full]"),
)

= AML 

#include "chapters/aml.typ"
#pagebreak()

= Constraint language

#include "chapters/constraints.typ"

#pagebreak() 

= Solver

#include "chapters/solver.typ"
