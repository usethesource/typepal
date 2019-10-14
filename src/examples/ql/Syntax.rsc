module examples::ql::Syntax

// Questionnaire Language QL, taken from https://github.com/cwi-swat/demoqles

start syntax Form
  = form: "form" Id name "{" Question* questions "}"
  ;

syntax Question
  = question: Label label Var var ":" Type type Value? value
  | computed: Label label Var var ":" Type type "=" Expr expr Value? value
  | ifThen: "if" "(" Expr cond ")" Question () !>> "else"
  | ifThenElse: "if" "(" Expr cond ")" Question question "else" Question elseQuestion
  | @Foldable group: "{" Question* questions "}"
  | @Foldable @category="Comment" invisible: "(" Question* questions ")"
  ;

syntax Value
  = "[" Const "]"
  ;
  
syntax Const
  = @category="MetaAmbiguity" Expr!var!not!mul!div!add!sub!lt!leq!gt!geq!eq!neq!and!or
  ;

syntax Expr
  = var: Id name
  | integer: Integer
  | string: String
  | money: Money
  | boolean: Boolean
  | bracket "(" Expr ")"
  > not: "!" Expr
  > left (
      mul: Expr "*" Expr
    | div: Expr "/" Expr
  )
  > left (
      add: Expr "+" Expr
    | sub: Expr "-" Expr
  )
  > non-assoc (
      lt: Expr "\<" Expr
    | leq: Expr "\<=" Expr
    | gt: Expr "\>" Expr
    | geq: Expr "\>=" Expr
    | eq: Expr "==" Expr
    | neq: Expr "!=" Expr
  )
  > left and: Expr "&&" Expr
  > left or: Expr "||" Expr
  ;
  
keyword Keywords = "true" | "false" ;

lexical Var = Id;

lexical Label = @category="Constant" label: String; 
  
syntax Type
  = "boolean" 
  | "string"
  | "integer"
  | "money"
  ;

lexical String = [\"] StrChar* [\"];

lexical StrChar
  = ![\"\\]
  | [\\][\\\"nfbtr]
  ;

lexical Boolean = "true" | "false";

lexical Integer =  [\-]? [0-9]+ !>> [0-9];

lexical Money =  [\-]? [0-9]+ "." [0-9]* !>> [0-9] ;

layout Standard = WhitespaceOrComment* !>> [\ \t\n\f\r] !>> "//" !>> "/*";
  
syntax Comment 
  = LineComment
  | CStart CommentChar* CEnd
  ;

lexical LineComment
  = @category="Comment" "//" ![\n\r]* $;

syntax CStart = @category="Comment" "/*";
syntax CEnd = @category="Comment" "*/";


syntax CommentChar 
  = @category="Comment" ![*{}\ \t\n\f\r]
  | @category="Comment" [*] !>> [/]
  | Embed
  ;

syntax Embed
  = "{" Expr expr "}"
  ;

syntax WhitespaceOrComment 
  = whitespace: Whitespace
  | comment: Comment
  ;   

lexical Whitespace 
  = [\u0009-\u000D \u0020 \u0085 \u00A0 \u1680 \u180E \u2000-\u200A \u2028 \u2029 \u202F \u205F \u3000]
  ; 
  
lexical Id 
  = ([a-z A-Z 0-9 _] !<< [a-z A-Z][\-a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Keywords
  ;