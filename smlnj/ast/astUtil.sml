functor MkExtAST(A: AST
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

functor MkASTMap(A: AST_EXT) : MAPPABLE =
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
       | FlatAppExpF x => FlatAppExpF $ List.map (fixityMap f) x
       | AppExpF {function=g, argument=x} =>
           AppExpF {function=f g, argument=f x}
       | CaseExpF {expr=x, rules=rl} =>
           CaseExpF {expr=f x, rules=List.map (ruleFmap f) rl}
       | LetExpF {dec=dc, expr=x} => LetExpF {dec=decMap f dc, expr=f x}
       | SeqExpF s => SeqExpF $ List.map f s
       | IntExpF l => IntExpF l
       | WordExpF l => WordExpF l
       | RealExpF s => RealExpF s
       | StringExpF s => StringExpF s
       | CharExpF s => CharExpF s
       | RecordExpF r => RecordExpF $ List.map (second $ f) r
       | ListExpF l => ListExpF $ List.map f l
       | TupleExpF l => TupleExpF $ List.map f l
       | SelectorExpF s => SelectorExpF s
       | ConstraintExpF {expr=x, constraint=ty} =>
           ConstraintExpF {expr=f x, constraint=ty}
       | HandleExpF {expr=x, rules=rl} =>
           HandleExpF {expr=f x, rules=List.map (ruleFmap f) rl}
       | RaiseExpF x => RaiseExpF (f x)
       | IfExpF {test=x, thenCase=t, elseCase=e} =>
           IfExpF {test=f x, thenCase=f t, elseCase=f e}
       | AndalsoExpF (x,y) => AndalsoExpF (f x, f y)
       | OrelseExpF (x,y) => OrelseExpF (f x, f y)
       | VectorExpF v => VectorExpF $ List.map f v
       | WhileExpF {test=x, expr=e} => WhileExpF {test=f x, expr=f e}
       | MarkExpF (x, r) => MarkExpF (f x, r)
  and ruleFmap (f:'a -> 'b) (RuleF {pat=pat, exp=e}:'a ruleF) : 'b ruleF =
    RuleF {pat=pat, exp=f e}
  and decMap (f:'a -> 'b) (dc:'a decF) : 'b decF =
    case dc
      of ValDecF (vbL, tyvs) => ValDecF (List.map (vbMap f) vbL, tyvs)
       | ValrecDecF (rvbL, tyvs) => ValrecDecF (List.map (rvbMap f) rvbL, tyvs)
       | FunDecF (fbL, tyvs) => FunDecF (List.map (fbMap f) fbL, tyvs)
       | TypeDecF t => TypeDecF t
       | DatatypeDecF dt => DatatypeDecF dt
       | DataReplDecF sp => DataReplDecF sp
       | DoDecF e => DoDecF $ f e
       | AbstypeDecF {abstycs=d, withtycs=tl, body=dcl} =>
           AbstypeDecF {abstycs=d, withtycs=tl, body=decMap f dcl}
       | ExceptionDecF el => ExceptionDecF el
       | StrDecF sl => StrDecF sl
       | AbsDecF sl => AbsDecF sl
       | FctDecF fl => FctDecF fl
       | SigDecF sl => SigDecF sl
       | FsigDecF sl => FsigDecF sl
       | LocalDecF (d1, d2) => LocalDecF (decMap f d1, decMap f d2)
       | SeqDecF dls => SeqDecF $ List.map (decMap f) dls
       | OpenDecF pl => OpenDecF pl
       | OvldDecF (sym, t, es) => OvldDecF (sym, t, List.map f es)
       | FixDecF fs => FixDecF fs
       | MarkDecF (dc', rg) => MarkDecF (decMap f dc', rg)
  and vbMap f v =
    case v
      of VbF {pat=p, exp=e, lazyp=b} => VbF {pat=p, exp=f e, lazyp=b}
       | MarkVbF (v', r) => MarkVbF (vbMap f v', r)
  and rvbMap f v =
    case v
      of RvbF {var=s, fixity=fx, exp=e, resultty=t, lazyp=b} =>
           RvbF {var=s, fixity=fx, exp=f e, resultty=t, lazyp=b}
       | MarkRvbF (v', r) => MarkRvbF (rvbMap f v', r)
  and fbMap f fnc =
    case fnc
      of FbF (cl, b) => FbF (List.map (clauseMap f) cl, b)
       | MarkFbF (fnc', r) => MarkFbF (fbMap f fnc', r)
  and clauseMap f (ClauseF {pats=p, resultty=t, exp=e}) =
    ClauseF {pats=p, resultty=t, exp=f e}
end

structure ASTUtil : AST_UTIL = struct
  structure A = Ast
  structure A' = MkExtAST(Ast)
  structure M = MkASTMap(A')
  structure T = MkTraverse(M)

  open A'
  open M
  open T

  infixr 0 $
  fun f $ x = f x

  fun first f (x,y) = (f x, y)
  fun second f (x,y) = (x, f y)


  type expr = t

  fun into' (a: A.exp) : A.exp expF =
    case a
      of A.VarExp p => VarExpF p
       | A.FnExp rl => FnExpF $ List.map ruleInto rl
       | A.FlatAppExp es => FlatAppExpF es
       | A.AppExp {function=f, argument=arg} =>
           AppExpF {function=f, argument=arg}
       | A.CaseExp {expr=e, rules=rl} =>
           CaseExpF {expr=e, rules=List.map ruleInto rl}
       | A.LetExp {dec=dc, expr=e} => LetExpF {dec=decInto dc, expr=e}
       | A.SeqExp l => SeqExpF l
       | A.IntExp l => IntExpF l
       | A.WordExp l => WordExpF l
       | A.RealExp l => RealExpF l
       | A.StringExp s => StringExpF s
       | A.CharExp s => CharExpF s
       | A.RecordExp r => RecordExpF r
       | A.ListExp l => ListExpF l
       | A.TupleExp l => TupleExpF l
       | A.SelectorExp s => SelectorExpF s
       | A.ConstraintExp {expr=e, constraint=ty} =>
           ConstraintExpF {expr=e, constraint=ty}
       | A.HandleExp {expr=e, rules=rl} =>
           HandleExpF {expr=e, rules=List.map ruleInto rl}
       | A.RaiseExp e => RaiseExpF e
       | A.IfExp {test=t, thenCase=e1, elseCase=e2} =>
           IfExpF {test=t, thenCase=e1, elseCase=e2}
       | A.AndalsoExp (e1, e2) => AndalsoExpF (e1, e2)
       | A.OrelseExp (e1, e2) => OrelseExpF (e1, e2)
       | A.VectorExp v => VectorExpF v
       | A.WhileExp {test=t, expr=e} => WhileExpF {test=t, expr=e}
       | A.MarkExp (e, r) => MarkExpF (e, r)
  and ruleInto (A.Rule {pat=pat, exp=e}) = RuleF {pat=pat, exp=e}
  and decInto (d: A.dec) : A.exp decF =
    case d
      of A.ValDec (vbs, tyvs) => ValDecF (List.map vbInto vbs, tyvs)
       | A.ValrecDec (rvbs, tyvs) => ValrecDecF (List.map rvbInto rvbs, tyvs)
       | A.FunDec (fbs, tyvs) => FunDecF (List.map fbInto fbs, tyvs)
       | A.TypeDec tbs => TypeDecF tbs
       | A.DatatypeDec dtdf => DatatypeDecF dtdf
       | A.DataReplDec sp => DataReplDecF sp
       | A.DoDec d => DoDecF d
       | A.AbstypeDec {abstycs=at, withtycs=tb, body=b} =>
           AbstypeDecF {abstycs=at, withtycs=tb, body=decInto b}
       | A.ExceptionDec es => ExceptionDecF es
       | A.StrDec ss => StrDecF ss
       | A.AbsDec ss => AbsDecF ss
       | A.FctDec fs => FctDecF fs
       | A.SigDec ss => SigDecF ss
       | A.FsigDec fss => FsigDecF fss
       | A.LocalDec (d1, d2) => LocalDecF (decInto d1, decInto d2)
       | A.SeqDec sf => SeqDecF $ List.map decInto sf
       | A.OpenDec ps => OpenDecF ps
       | A.OvldDec (s,t,es) => OvldDecF (s,t,es)
       | A.FixDec ff => FixDecF ff
       | A.MarkDec (mdf, r) => MarkDecF (decInto mdf, r)
  and vbInto (vb : A.vb) =
    case vb
      of A.Vb {exp=e, lazyp=b, pat=pat} => VbF {exp=e, lazyp=b, pat=pat}
       | A.MarkVb (v,r) => MarkVbF (vbInto v, r)
  and rvbInto (rvb : A.rvb) =
    case rvb
      of A.Rvb rv => RvbF rv
       | A.MarkRvb (rv, rg) => MarkRvbF (rvbInto rv, rg)
  and fbInto (fb : A.fb) =
    case fb
      of A.Fb (fv,b) => FbF (List.map clauseInto fv, b)
       | A.MarkFb (af, rg) => MarkFbF (fbInto af, rg)
  and clauseInto (Clause cf) = ClauseF cf

  fun into a = ana into' a

  fun out' (a: A.exp expF) : A.exp =
    case a
      of VarExpF p => A.VarExp p
       | FnExpF rl => A.FnExp $ List.map ruleOut rl
       | FlatAppExpF es => A.FlatAppExp es
       | AppExpF {function=f, argument=arg} =>
           A.AppExp {function=f, argument=arg}
       | CaseExpF {expr=e, rules=rl} =>
           A.CaseExp {expr=e, rules=List.map ruleOut rl}
       | LetExpF {dec=dc, expr=e} => A.LetExp {dec=decOut dc, expr=e}
       | SeqExpF l => A.SeqExp l
       | IntExpF l => A.IntExp l
       | WordExpF l => A.WordExp l
       | RealExpF l => A.RealExp l
       | StringExpF s => A.StringExp s
       | CharExpF s => A.CharExp s
       | RecordExpF r => A.RecordExp r
       | ListExpF l => A.ListExp l
       | TupleExpF l => A.TupleExp l
       | SelectorExpF s => A.SelectorExp s
       | ConstraintExpF {expr=e, constraint=ty} =>
           A.ConstraintExp {expr=e, constraint=ty}
       | HandleExpF {expr=e, rules=rl} =>
           A.HandleExp {expr=e, rules=List.map ruleOut rl}
       | RaiseExpF e => A.RaiseExp e
       | IfExpF {test=t, thenCase=e1, elseCase=e2} =>
           A.IfExp {test=t, thenCase=e1, elseCase=e2}
       | AndalsoExpF (e1, e2) => A.AndalsoExp (e1, e2)
       | OrelseExpF (e1, e2) => A.OrelseExp (e1, e2)
       | VectorExpF v => A.VectorExp v
       | WhileExpF {test=t, expr=e} => A.WhileExp {test=t, expr=e}
       | MarkExpF (e, r) => A.MarkExp (e, r)
  and ruleOut (RuleF {pat=pat, exp=e}) = A.Rule {pat=pat, exp=e}
  and decOut (d: A.exp decF) : A.dec =
    case d
      of ValDecF (vbs, tyvs) => A.ValDec (List.map vbOut vbs, tyvs)
       | ValrecDecF (rvbs, tyvs) => A.ValrecDec (List.map rvbOut rvbs, tyvs)
       | FunDecF (fbs, tyvs) => A.FunDec (List.map fbOut fbs, tyvs)
       | TypeDecF tbs => A.TypeDec tbs
       | DatatypeDecF dtdf => A.DatatypeDec dtdf
       | DataReplDecF sp => A.DataReplDec sp
       | DoDecF d => A.DoDec d
       | AbstypeDecF {abstycs=at, withtycs=tb, body=b} =>
           A.AbstypeDec {abstycs=at, withtycs=tb, body=decOut b}
       | ExceptionDecF es => A.ExceptionDec es
       | StrDecF ss => A.StrDec ss
       | AbsDecF ss => A.AbsDec ss
       | FctDecF fs => A.FctDec fs
       | SigDecF ss => A.SigDec ss
       | FsigDecF fss => A.FsigDec fss
       | LocalDecF (d1, d2) => A.LocalDec (decOut d1, decOut d2)
       | SeqDecF sf => A.SeqDec $ List.map decOut sf
       | OpenDecF ps => A.OpenDec ps
       | OvldDecF (s,t,es) => A.OvldDec (s,t,es)
       | FixDecF ff => A.FixDec ff
       | MarkDecF (mdf, r) => A.MarkDec (decOut mdf, r)
  and vbOut (vb : A.exp vbF) =
    case vb
      of VbF {exp=e, lazyp=b, pat=pat} => A.Vb {exp=e, lazyp=b, pat=pat}
       | MarkVbF (v,r) => A.MarkVb (vbOut v, r)
  and rvbOut (rvb : A.exp rvbF) =
    case rvb
      of RvbF rv => A.Rvb rv
       | MarkRvbF (rv, rg) => A.MarkRvb (rvbOut rv, rg)
  and fbOut (fb : A.exp fbF) =
    case fb
      of FbF (fv,b) => A.Fb (List.map clauseOut fv, b)
       | MarkFbF (af, rg) => A.MarkFb (fbOut af, rg)
  and clauseOut (ClauseF cf) = A.Clause cf

  fun out x = cata out' x
end

