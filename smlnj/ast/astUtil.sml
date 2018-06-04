functor ExtAST(A: AST
  where type srcpos = int
  and type region = int * int
  and type 'a fixitem = {item:'a, fixity:Symbol.symbol option, region:int*int}
) : AST_EXT =
struct
  open A

  fun fixityMap (f:'a -> 'b)
    ({item=x, fixity=fx, region=rg}: 'a fixitem)
  : 'b fixitem =
    {item=f x, fixity=fx, region=rg}

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

functor ASTMap(A: AST_EXT) : MAPPABLE =
struct
  open A

  infixr 0 $
  fun f $ x = f x

  fun first f (x,y) = (f x, y)
  fun second f (x,y) = (x, f y)

  type 'a t = 'a expF

  fun fmap (f:'a -> 'b) (a:'a expF) : 'b expF =
    case a
      of VarExpF p => VarExpF p
       | FnExpF rl => FnExpF $ List.map (ruleFmap f) rl
       | FlatAppExpF x => FlatAppExpF (List.map (fixityMap (fmap f)) x)
       | AppExpF {function=g, argument=x} =>
           AppExpF {function=fmap f g, argument=fmap f x}
       | CaseExpF {expr=x, rules=rl} =>
           CaseExpF {expr=fmap f x, rules=List.map (ruleFmap f) rl}
       | LetExpF {dec=dc, expr=x} => LetExpF {dec=dc, expr=fmap f x}
       | SeqExpF s => SeqExpF $ List.map (fmap f) s
       | IntExpF l => IntExpF l
       | WordExpF l => WordExpF l
       | RealExpF s => RealExpF s
       | StringExpF s => StringExpF s
       | CharExpF s => CharExpF s
       | RecordExpF r => RecordExpF $ List.map (second $ fmap f) r
       | ListExpF l => ListExpF $ List.map (fmap f) l
       | TupleExpF l => TupleExpF $ List.map (fmap f) l
       | SelectorExpF s => SelectorExpF s
       | ConstraintExpF {expr=x, constraint=ty} =>
           ConstraintExpF {expr=fmap f x, constraint=ty}
       | HandleExpF {expr=x, rules=rl} =>
           HandleExpF {expr=fmap f x, rules=List.map (ruleFmap f) rl}
       | RaiseExpF x => RaiseExpF (fmap f x)
       | IfExpF {test=x, thenCase=t, elseCase=e} =>
           IfExpF {test=fmap f x, thenCase=fmap f t, elseCase=fmap f e}
       | AndalsoExpF (x,y) => AndalsoExpF (fmap f x, fmap f y)
       | OrelseExpF (x,y) => OrelseExpF (fmap f x, fmap f y)
       | VectorExpF v => VectorExpF $ List.map (fmap f) v
       | WhileExpF {test=x, expr=e} => WhileExpF {test=fmap f x, expr=fmap f e}
       | MarkExpF (x, r) => MarkExpF (fmap f x, r)
  and ruleFmap (f:'a -> 'b) (RuleF {pat=pat, exp=e}:'a ruleF) : 'b ruleF =
    RuleF {pat=pat, exp=fmap f e}
end

structure ASTUtil : AST_UTIL = struct
  structure A = Ast
  structure A' = ExtAST(Ast)
  structure M = ASTMap(A')
  structure T = Traverse(M)

  open A'
  open M
  open T

  infixr 0 $
  fun f $ x = f x

  fun first f (x,y) = (f x, y)
  fun second f (x,y) = (x, f y)


  type expr = t

  fun into' a =
    case a
      of A.VarExp p => VarExpF p
       | A.FnExp rl => FnExpF $ List.map ruleInto rl
       | A.FlatAppExp es => FlatAppExpF $ List.map (A'.fixityMap into') es
       | A.AppExp {function=f, argument=arg} =>
           AppExpF {function=into' f, argument=into' arg}
       | A.CaseExp {expr=e, rules=rl} =>
           CaseExpF {expr=into' e, rules=List.map ruleInto rl}
       | A.LetExp {dec=dc, expr=e} => LetExpF {dec=dc, expr=into' e}
       | A.SeqExp l => SeqExpF $ List.map into' l
       | A.IntExp l => IntExpF l
       | A.WordExp l => WordExpF l
       | A.RealExp l => RealExpF l
       | A.StringExp s => StringExpF s
       | A.CharExp s => CharExpF s
       | A.RecordExp r => RecordExpF $ List.map (second into') r
       | A.ListExp l => ListExpF $ List.map into' l
       | A.TupleExp l => TupleExpF $ List.map into' l
       | A.SelectorExp s => SelectorExpF s
       | A.ConstraintExp {expr=e, constraint=ty} =>
           ConstraintExpF {expr=into' e, constraint=ty}
       | A.HandleExp {expr=e, rules=rl} =>
           HandleExpF {expr=into' e, rules=List.map ruleInto rl}
       | A.RaiseExp e => RaiseExpF $ into' e
       | A.IfExp {test=t, thenCase=e1, elseCase=e2} =>
           IfExpF {test=into' t, thenCase=into' e1, elseCase=into' e2}
       | A.AndalsoExp (e1, e2) => AndalsoExpF (into' e1, into' e2)
       | A.OrelseExp (e1, e2) => OrelseExpF (into' e1, into' e2)
       | A.VectorExp v => VectorExpF $ List.map into' v
       | A.WhileExp {test=t, expr=e} => WhileExpF {test=into' t, expr=into' e}
       | A.MarkExp (e, r) => MarkExpF (into' e, r)
  and ruleInto (A.Rule {pat=pat, exp=e}) = RuleF {pat=pat, exp=into' e}

  val into = inj o into'

  fun out a =
    case prj a
      of VarExpF p => A.VarExp p
       | FnExpF rl => A.FnExp $ List.map ruleOut rl
       | FlatAppExpF es => A.FlatAppExp $ List.map (A'.fixityMap out') es
       | AppExpF {function=f, argument=arg} =>
           A.AppExp {function=out' f, argument=out' arg}
       | CaseExpF {expr=e, rules=rl} =>
           A.CaseExp {expr=out' e, rules=List.map ruleOut rl}
       | LetExpF {dec=dc, expr=e} => A.LetExp {dec=dc, expr=out' e}
       | SeqExpF l => A.SeqExp $ List.map out' l
       | IntExpF l => A.IntExp l
       | WordExpF l => A.WordExp l
       | RealExpF l => A.RealExp l
       | StringExpF s => A.StringExp s
       | CharExpF s => A.CharExp s
       | RecordExpF r => A.RecordExp $ List.map (second out') r
       | ListExpF l => A.ListExp $ List.map out' l
       | TupleExpF l => A.TupleExp $ List.map out' l
       | SelectorExpF s => A.SelectorExp s
       | ConstraintExpF {expr=e, constraint=ty} =>
           A.ConstraintExp {expr=out' e, constraint=ty}
       | HandleExpF {expr=e, rules=rl} =>
           A.HandleExp {expr=out' e, rules=List.map ruleOut rl}
       | RaiseExpF e => A.RaiseExp $ out' e
       | IfExpF {test=t, thenCase=e1, elseCase=e2} =>
           A.IfExp {test=out' t, thenCase=out' e1, elseCase=out' e2}
       | AndalsoExpF (e1, e2) => A.AndalsoExp (out' e1, out' e2)
       | OrelseExpF (e1, e2) => A.OrelseExp (out' e1, out' e2)
       | VectorExpF v => A.VectorExp $ List.map out' v
       | WhileExpF {test=t, expr=e} => A.WhileExp {test=out' t, expr=out' e}
       | MarkExpF (e, r) => A.MarkExp (out' e, r)
  and ruleOut (RuleF {pat=pat, exp=e}) = A.Rule {pat=pat, exp=out' e}
  and out' x = (out o inj) x
end

