signature AST_EXT = sig
  include AST

  val fixityMap : ('a -> 'b) -> 'a fixitem -> 'b fixitem

  datatype 'a expF =
      VarExpF of path
    | FnExpF of 'a ruleF list
    | FlatAppExpF of 'a fixitem list
    | AppExpF of {function : 'a, argument : 'a}
    | CaseExpF of {expr : 'a, rules : 'a ruleF list}
    | LetExpF of {dec : 'a decF, expr : 'a}
    | SeqExpF of 'a list
    | IntExpF of literal
    | WordExpF of literal
    | RealExpF of string
    | StringExpF of string
    | CharExpF of string
    | RecordExpF of (symbol * 'a) list
    | ListExpF of 'a list
    | TupleExpF of 'a list
    | SelectorExpF of symbol
    | ConstraintExpF of {expr : 'a, constraint : ty}
    | HandleExpF of {expr : 'a, rules : 'a ruleF list}
    | RaiseExpF of 'a
    | IfExpF of {test : 'a, thenCase : 'a, elseCase : 'a}
    | AndalsoExpF of ('a * 'a)
    | OrelseExpF of ('a * 'a)
    | VectorExpF of 'a list
    | WhileExpF of {test : 'a, expr : 'a}
    | MarkExpF of ('a * region)
  and 'a ruleF = RuleF of {pat: pat, exp: 'a}
  and 'a decF =
      ValDecF of ('a vbF list * tyvar list)
    | ValrecDecF of ('a rvbF list * tyvar list)
    | FunDecF of ('a fbF list * tyvar list)
    | TypeDecF of tb list
    | DatatypeDecF of {datatycs : db list, withtycs : tb list}
    | DataReplDecF of symbol * path
    | DoDecF of 'a
    | AbstypeDecF of {abstycs : db list, withtycs : tb list, body : 'a decF}
    | ExceptionDecF of eb list
    | StrDecF of strb list
    | AbsDecF of strb list
    | FctDecF of fctb list
    | SigDecF of sigb list
    | FsigDecF of fsigb list
    | LocalDecF of ('a decF * 'a decF)
    | SeqDecF of 'a decF list
    | OpenDecF of path list
    | OvldDecF of (symbol * ty * 'a list)
    | FixDecF of {fixity : fixity, ops : symbol list}
    | MarkDecF of ('a decF * region)
  and 'a vbF =
      VbF of {pat : pat, exp : 'a, lazyp : bool}
    | MarkVbF of 'a vbF * region
  and 'a rvbF =
      RvbF of {var : symbol, fixity : (symbol * region) option,
               exp : 'a, resultty : ty option, lazyp : bool}
    | MarkRvbF of 'a rvbF * region
  and 'a fbF =
      FbF of 'a clauseF list * bool
    | MarkFbF of 'a fbF * region
  and 'a clauseF =
      ClauseF of {pats : pat fixitem list, resultty : ty option, exp : 'a}
end

