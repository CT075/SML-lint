signature AST_EXT = sig
  include AST

  val fixityMap : ('a -> 'b) -> 'a fixitem -> 'b fixitem

  datatype 'a expF =
      VarExpF of path
    | FnExpF of 'a ruleF list
    | FlatAppExpF of 'a expF fixitem list
    | AppExpF of {function : 'a expF, argument : 'a expF}
    | CaseExpF of {expr : 'a expF, rules : 'a ruleF list}
    | LetExpF of {dec : dec, expr : 'a expF}
    | SeqExpF of 'a expF list
    | IntExpF of literal
    | WordExpF of literal
    | RealExpF of string
    | StringExpF of string
    | CharExpF of string
    | RecordExpF of (symbol * 'a expF) list
    | ListExpF of 'a expF list
    | TupleExpF of 'a expF list
    | SelectorExpF of symbol
    | ConstraintExpF of {expr : 'a expF, constraint : ty}
    | HandleExpF of {expr : 'a expF, rules : 'a ruleF list}
    | RaiseExpF of 'a expF
    | IfExpF of {test : 'a expF, thenCase : 'a expF, elseCase : 'a expF}
    | AndalsoExpF of ('a expF * 'a expF)
    | OrelseExpF of ('a expF * 'a expF)
    | VectorExpF of 'a expF list
    | WhileExpF of {test : 'a expF, expr : 'a expF}
    | MarkExpF of ('a expF * region)
  and 'a ruleF = RuleF of {pat: pat, exp: 'a expF}
end


