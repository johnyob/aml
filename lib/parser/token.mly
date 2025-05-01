// end of file
%token EOF

// keywords
%token LET "let"
%token IN "in"
%token FUN "fun"
%token MATCH "match"
%token WITH "with"
%token FORALL "forall"
%token TYPE "type"
%token EXTERNAL "external"
%token REFL "Refl"
%token SEMI_SEMI_COLON ";;"
%token BOT "bot"
%token ABSURD "absurd" 

// operators
%token RIGHT_ARROW "->"
%token COLON ":"
%token EQUAL "="
%token DOT "."
%token COMMA ","
%token QUOTE "'"

// constants
%token CONST_TRUE "true"
%token CONST_FALSE "false"
%token CONST_UNIT "()"
%token <int> CONST_INT "<int>"

// identifiers
%token <string> IDENT "<ident>"

// parens
%token LEFT_PAREN "("
%token RIGHT_PAREN ")"

%%