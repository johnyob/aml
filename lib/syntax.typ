#let textsf = text.with(font: "roboto")
#let dom = textsf("dom")
#let tforall(alpha) = $forall #alpha. med$
#let tforallb(alpha, bound) = $forall (#alpha >= #bound). med$

#let is-content = this => {
  type(this) == str or type(this) == content or type(this) == symbol
}

#let syntax-rule(
  // The name of the syntax rule, displayed to the left of the definition
  name: none,
  // The BNF grammar rule
  grammar
) = {
  assert(
    is-content(name),
    message: "The name of the syntax rule must be some content.",
  )

  (
    name: name,
    grammar: grammar,
  )
}

#let is-syntax-rule = this => {
  type(this) == dictionary and "name" in this and is-content(this.name) and "grammar" in this
}

// Lays out a syntax definition
#let syntax(
  // The space between each consequtive rule
  horizontal-spacing: 5cm,
  // The space between rule names and the rules themselves
  vertical-spacing: 5mm,
  // The rules the define the syntax
  ..rules
) = {
  let rules = rules.pos()
  assert(
    rules.all(is-syntax-rule),
    message: "Each rule must be a syntax rule defined by #syntax-rule",
  )

  block(
    width: 80%,
    grid(
      columns: (auto, auto),
      rows: auto,
      column-gutter: horizontal-spacing,
      row-gutter: vertical-spacing,
      align: (left, left),
      ..rules.map(rule => (rule.name, rule.grammar)).flatten()
    ),
  )

}