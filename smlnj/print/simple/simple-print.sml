Control.Elab.unusedBindingWarn := false;
CM.make "$smlnj/viscomp/basics.cm";
CM.make "$smlnj/viscomp/elabdata.cm";

signature LINT =
sig
  val parseFile : string -> Ast.dec * StaticEnv.staticEnv
  val pp_pat : Ast.pat -> string
  val pp_exp : Ast.exp -> StaticEnv.staticEnv -> string
  val pp_dec : Ast.dec -> StaticEnv.staticEnv -> string
end

structure Lint : LINT =
struct
   open Ast Fixity VarCon Types Tuples

   (* PARSING *)
   fun parseFile filename =
       let
         val stream = TextIO.openIn filename
         val interactive = false
         val consumer = ErrorMsg.defaultConsumer ()
         val source = Source.newSource (filename, stream, interactive, consumer)
         val ast = SmlFile.parse source

         val compManagerHook : {
           manageImport : Ast.dec * EnvRef.envref -> unit,
           managePrint :  Symbol.symbol * EnvRef.envref -> unit,
           getPending : unit -> Symbol.symbol list
         } ref = ref {
               manageImport = fn _ => (),
               managePrint = fn _ => (),
               getPending = fn () => []
             }

         val loc = EnvRef.loc ()
         val base = EnvRef.base ()
         val _ = #manageImport (!compManagerHook) (ast, loc)

         fun getenv () = Environment.layerEnv (#get loc (), #get base ())
         val env = #static (getenv ())
       in
         (ast, env)
       end


   (* FORMATTING *)
   fun intercalate sym [] = ""
     | intercalate sym (x::xs) =
       let
         fun intercalate' sym [] = ""
           | intercalate' sym (y::ys) = sym ^ y ^ (intercalate' sym ys)
       in
         x ^ (intercalate' sym xs)
       end

   fun pp_seq sep pr seq =
       intercalate sep (map pr seq)

   fun lpcond atom = if atom then "(" else ""
   fun rpcond atom = if atom then ")" else ""

   (* TUPLES *)
   fun checkpat (n,nil) = true
     | checkpat (n, (sym,_)::fields) = Symbol.eq(sym, numlabel n) andalso checkpat(n+1,fields)

   fun checkexp (n, nil) = true
     | checkexp (n, (sym,exp)::fields) =
       Symbol.eq(sym, numlabel n) andalso checkexp (n+1, fields)

   fun isTUPLEpat (RecordPat{def=[_],...}) = false
     | isTUPLEpat (RecordPat{def=defs,flexibility=false}) = checkpat(1,defs)
     | isTUPLEpat _ = false

   fun isTUPLEexp (RecordExp[_]) = false
     | isTUPLEexp (RecordExp fields) = checkexp(1,fields)
     | isTUPLEexp (MarkExp(a,_)) = isTUPLEexp a
     | isTUPLEexp _ = false

   (* FIXITY *)
   fun lookFIX (env,sym) =
       Lookup.lookFix (env,Symbol.fixSymbol(Symbol.name sym))

   val nullFix = INfix(0,0)
   val infFix = INfix(1000000,100000)
   fun strongerL(INfix(_,m),INfix(n,_)) = m >= n
     | strongerL  _ = false                 (* should not matter *)
   fun strongerR(INfix(_,m),INfix(n,_)) = n > m
     | strongerR _ = true                  (* should not matter *)

   (* SYMBOL *)
   fun pp_sym s = Symbol.name s

   fun pp_symbol_list symbols =
       pp_seq "." pp_sym symbols


   (* TYPES *)
   fun ppTyvar tyv =
       case tyv of
           Tyv s => pp_sym s
         | MarkTyv (t, r) => ppTyvar t

   fun pp_typ typ =
       let
         fun strength ty =
             case ty of
                 VarTy(_) => 1
              |  ConTy(tycon, args) =>
                 (case tycon
                   of [tyc] =>
                      if Symbol.eq(Symbol.tycSymbol("->"), tyc) then 0
                      else 2
                   |  _ => 2)
              |  RecordTy _ => 2
              |  TupleTy _ => 1
              |  _ => 2

         fun ppTypeArgs tys =
             case tys of
                 [] => ""
               | [ty] =>
                 if strength ty <= 1
                 then "(" ^ pp_typ ty ^ ")"
                 else pp_typ ty
               | _ =>
                 "("
                 ^ pp_seq "," pp_typ tys
                 ^ ")"
       in
         case typ of
             VarTy t => ppTyvar t
           | ConTy (tycon, []) => pp_symbol_list tycon
           | ConTy (tycon, args) =>
             (case tycon of
                  [tyc] =>
                  if Symbol.eq (Symbol.tycSymbol("->"), tyc)
                  then (case args of
                            [dom, ran] => pp_typ dom
                                          ^ " -> "
                                          ^ pp_typ ran
                          | _ => raise Fail "-> tycon needs 2 args")
                  else ppTypeArgs args
                       ^ pp_sym tyc
                | _ => ppTypeArgs args
                       ^ pp_symbol_list tycon)
           | RecordTy s =>
             "{"
             ^ pp_seq "," (fn (sym, tv) => pp_sym sym ^ ":" ^ pp_typ tv) s
             ^ "}"
           | TupleTy t =>
             "("
             ^ pp_seq " * " pp_typ t
           | MarkTy (t, r) => pp_typ t
       end

   (* PATTERNS *)
   fun pp_pat pat =
       case pat of
           WildPat => "_"
         | VarPat p => pp_symbol_list p
         | IntPat i => IntInf.toString i
         | WordPat w => "0w" ^ IntInf.toString w
         | StringPat s => "\"" ^ s ^ "\""
         | CharPat c => "#" ^  "\"" ^ c ^ "\""
         | LayeredPat {varPat, expPat} =>
           pp_pat varPat ^ " as " ^ pp_pat expPat
         | RecordPat {def=[], flexibility} =>
           if flexibility then "{...}"
           else "()"
         | (r as RecordPat {def, flexibility}) =>
           if isTUPLEpat r
           then "("
                ^ pp_seq "," (fn (sym, pat) => pp_pat pat) def
                ^ ")"
           else "{"
                ^ pp_seq "," (fn (sym, pat) => pp_sym sym ^ "=" ^ pp_pat pat) def
                ^ "}"
         | ListPat [] => "[]"
         | ListPat l => "["
                        ^ pp_seq "," pp_pat l
                        ^ "]"
         | TuplePat t => "("
                         ^ pp_seq "," pp_pat t
                         ^ ")"
         | FlatAppPat fap => pp_seq " " (fn {item, fixity, region} => pp_pat item) fap
         | ConstraintPat {pattern, constraint} => pp_pat pattern
                                                  ^ " : "
                                                  ^ pp_typ constraint
         | AppPat {constr, argument} => pp_pat constr ^ " as " ^ pp_pat argument
         | VectorPat [] => "#[]"
         | VectorPat v => "#["
                          ^ pp_seq "," pp_pat v
                          ^ "]"
         | MarkPat (pat, (s, e)) => pp_pat pat
         | OrPat orpat => "("
                          ^ pp_seq "| " pp_pat orpat
                          ^ ")"


   (* EXPRESSIONS *)

   fun pp_exp exp (env : StaticEnv.staticEnv) =
       let
         fun pp_exp' exp atom =
             case exp of
                 VarExp p => pp_symbol_list p
               | FnExp rules =>
                 "fn " ^ (pp_seq " | " (fn r => pp_rule r env) rules)
               | FlatAppExp fap =>
                 pp_seq " " (fn {item, fixity, region} => pp_exp' item true) fap
               | AppExp e => (lpcond atom)
                             ^ pp_app_exp (AppExp e, nullFix, nullFix) atom
                             ^ (rpcond atom)
               | CaseExp {expr, rules} =>
                 "(case "
                 ^ pp_exp' expr true
                 ^ "of \n"
                 ^ (pp_seq "\n | " (fn r => pp_rule r env) rules)
                 ^ ")"
               | LetExp {dec, expr} =>
                 " let\n"
                 ^ pp_dec dec env
                 ^ "\n in\n"
                 ^ pp_exp' expr false
                 ^ "\n end"
               | SeqExp exps =>
                 let
                   fun parenThunk () =
                       "("
                       ^ pp_seq ";" (fn exp => pp_exp' exp false) exps
                       ^ ")"
                   fun subExpCount (MarkExp (expr, _)) = subExpCount expr
                     | subExpCount (FlatAppExp subexps) = length subexps
                     | subExpCount _ = 1
                 in
                   case exps
                    of [expr] => if (subExpCount expr) < 2
                                 then pp_exp' expr false
                                 else parenThunk()
                     | _ => parenThunk()
                 end
               | IntExp i => IntInf.toString i
               | WordExp w => "0w" ^ IntInf.toString w
               | RealExp r => r
               | StringExp s => "\"" ^ s ^ "\""
               | CharExp c => "#" ^  "\"" ^ c ^ "\""
               | (r as RecordExp fields) =>
                 if isTUPLEexp r
                 then "("
                      ^ pp_seq "," (fn (_, exp) => pp_exp' exp false) fields
                      ^ ")"
                 else "{"
                      ^ pp_seq "," (fn (name, exp) => (pp_sym name) ^ "=" ^ pp_exp' exp false) fields
                      ^ "}"
               | ListExp p => "["
                              ^ pp_seq "," (fn exp => pp_exp' exp false) p
                              ^ "]"
               | TupleExp p => "("
                               ^ pp_seq "," (fn exp => pp_exp' exp false) p
                               ^ ")"
               | SelectorExp name =>
                 lpcond atom
                 ^ "#"
                 ^ pp_sym name
                 ^ rpcond atom
               | ConstraintExp {expr, constraint} =>
                 lpcond atom
                 ^ pp_exp' expr false
                 ^ ":"
                 ^ pp_typ constraint
                 ^ rpcond atom
               | HandleExp {expr, rules} =>
                 lpcond atom
                 ^ pp_exp' expr atom
                 ^ "handle "
                 ^ pp_seq "| " (fn r => pp_rule r env) rules
                 ^ rpcond atom
               | RaiseExp exp =>
                 lpcond atom
                 ^ "raise "
                 ^ pp_exp' exp true
                 ^ rpcond atom
               | IfExp {test, thenCase, elseCase} =>
                 lpcond atom
                 ^ "if "
                 ^ pp_exp' test false
                 ^ "then "
                 ^ pp_exp' thenCase false
                 ^ "else "
                 ^ pp_exp' elseCase false
                 ^ rpcond atom
               | AndalsoExp (e1, e2) =>
                 lpcond atom
                 ^ pp_exp' e1 true
                 ^ "andalso "
                 ^ pp_exp' e2 true
                 ^ rpcond atom
               | OrelseExp (e1, e2) =>
                 lpcond atom
                 ^ pp_exp' e1 true
                 ^ "orelse "
                 ^ pp_exp' e2 true
                 ^ rpcond atom
               | WhileExp {test, expr} =>
                 "while "
                 ^ pp_exp' test false
                 ^ "do "
                 ^ pp_exp' expr false
               | VectorExp [] => "#[]"
               | VectorExp exps =>
                 "#["
                 ^ pp_seq "," (fn exp => pp_exp' exp false) exps
                 ^ "]"
               | MarkExp (exp, (s, e)) =>
                 (* If we want to modify a file in place, then the
                  * source location information will be useful, so
                  * we'll want to change this *)
                 pp_exp' exp atom

         and pp_app_exp (exp, left, right) (atom : bool) =
             let
               fun stripMark (MarkExp(a,_)) = stripMark a
                 | stripMark x = x

               fun fixitypp(name, rand, leftFix, rightFix) =
                   let
                     val dname = SymPath.toString (SymPath.SPATH name)
                     val thisFix = case name of
                                       [id] => lookFIX (env, id)
                                     | _ => NONfix
                     fun prNon exp = pp_exp' exp true
                   in
                     case thisFix of
                         INfix _ =>  (case stripMark rand of
                                          RecordExp [(_, pl), (_, pr)] =>
                                          let
                                            val atom = strongerL (leftFix, thisFix)
                                                       orelse strongerR (thisFix, rightFix)
                                            val (left, right) = if atom then (nullFix, nullFix)
                                                                else (leftFix, rightFix)
                                          in
                                            lpcond atom
                                            ^ pp_app_exp (pl, left, thisFix) atom
                                            ^ " " ^ dname ^ " "
                                            ^ pp_app_exp (pr, thisFix, right) atom
                                            ^ rpcond atom
                                          end
                                        | e' => prNon e')
                       | NONfix => prNon rand
                   end

               fun appPrint (AppExp {function=rator, argument=rand}, l, r) =
                   (case stripMark rator of
                        VarExp v => fixitypp (v, rand, l, r)
                     |  rator => (pp_exp' rator atom) ^ " " ^ (pp_exp' rand atom))
                 | appPrint (MarkExp (exp, (s, e)), l, r) =
                   (* If we want to modify a file in place, then the
                    * source location information will be useful, so
                    * we'll want to change this *)
                   appPrint (exp, l, r)
                 | appPrint _ = raise Fail "Application invalid"
             in
               appPrint (exp, left, right)
             end
       in
         pp_exp' exp false
       end

   and pp_rule (Rule {pat, exp}) env =
        pp_pat pat
        ^ " => "
        ^ pp_exp exp env


   (* DECLARATIONS *)
   and pp_dec dec env =
       let
         fun pp_dec' dec =
             case dec of
                 ValDec (vbs, tyvars) =>
                 "val "
                 ^ pp_seq "and " (fn v => ppVb v env) vbs
               | ValrecDec (rvbs, tyvars) =>
                 "val rec "
                 ^ pp_seq "and " (fn r => ppRvb r env) rvbs
               | DoDec exp =>
                 "do "
                 ^ pp_exp exp env
               | FunDec (fbs, tyvars) =>
                 "fun "
                 ^ pp_seq "and " (fn f => ppFb f env) fbs
               | TypeDec tycs =>
                 "type "
                 ^ pp_seq " " ppTb tycs
               | DatatypeDec {datatycs, withtycs=[]} =>
                 "datatype "
                 ^ pp_seq " " ppDb datatycs
               | DatatypeDec {datatycs, withtycs} =>
                 "datatype "
                 ^ pp_seq " " ppDb datatycs
                 ^ "withtype "
                 ^ pp_seq " " ppTb withtycs
               | AbstypeDec {abstycs, withtycs=[], body} =>
                 "datatype "
                 ^ pp_seq " " ppDb abstycs
                 ^ "\n"
                 ^ pp_dec' body
               | AbstypeDec {abstycs, withtycs, body} =>
                 "datatype "
                 ^ pp_seq " " ppDb abstycs
                 ^ "\n"
                 ^ "withtype "
                 ^ pp_seq " " ppTb withtycs
                 ^ "\n"
                 ^ pp_dec' body
               | ExceptionDec ebs => pp_seq " " ppEb ebs
               | StrDec sbs => "<structure>"
               | AbsDec sbs => "<abstraction?>"
               | FctDec fbs => "<functor>"
               | SigDec sigvars => "<signature>"
               | FsigDec sigvars => "<functor signature>"
               | LocalDec (inner, outer) =>
                 "local\n"
                 ^ pp_dec' inner
                 ^ "\n" ^ "in\n"
                 ^ pp_dec' outer
                 ^ "\n" ^ "end"
               | SeqDec decs =>
                 pp_seq "\n" pp_dec' decs
               | OpenDec strbs =>
                 "open "
                 ^ pp_seq " " pp_symbol_list strbs
               | OvldDec (sym, ty, explist) => pp_sym sym
               | FixDec {fixity, ops} =>
                 (case fixity of
                      NONfix => "nonfix"
                    | INfix (i, _) =>
                      (if i mod 2 = 0
                       then "infix "
                       else "infixr ")
                      ^ (if i div 2 > 0
                         then Int.toString (i div 2)
                         else "")
                      ^ pp_seq " " pp_sym ops)
               | DataReplDec (sym, path) => "datatype "
                                            ^ pp_sym sym
                                            ^ " = "
                                            ^ "datatype "
                                            ^ pp_symbol_list path
               | MarkDec (dec, (s, e)) => pp_dec' dec
       in
         pp_dec' dec
       end

   (* BINDINGS *)
   and ppVb vb env =
       case vb of
           Vb {pat, exp, ...} =>
           pp_pat pat
           ^ " = "
           ^ pp_exp exp env
         | MarkVb (vb, region) => ppVb vb env

   and ppRvb rvb env =
       case rvb of
           Rvb {var, exp, ...} =>
           pp_sym var
           ^ " = "
           ^ pp_exp exp env
         | MarkRvb (rvb, region) => ppRvb rvb env

   and ppFb fb env =
       case fb of
           Fb (clauses, ops) =>
           pp_seq "  | " (fn c => ppClause c env) clauses
         | MarkFb (fb, region) => ppFb fb env

   and ppClause cls env =
       case cls of
           Clause {pats, resultty, exp} =>
           let
             fun ppCls {item, fixity, region} =
                 case fixity of
                     SOME a => pp_pat item
                   | NONE => (case item of
                                  FlatAppPat p => "(" ^ pp_pat item ^ ")"
                                | ConstraintPat p => "(" ^ pp_pat item ^ ")"
                                | LayeredPat p => "(" ^ pp_pat item ^ ")"
                                | OrPat p => "(" ^ pp_pat item ^ ")"
                                | _ => pp_pat item)
           in
             pp_seq " " ppCls pats
             ^ (case resultty of
                    SOME ty => ":" ^ pp_typ ty
                  | NONE => "")
             ^ " ="
             ^ pp_exp exp env
           end

   and ppTb tb =
       let
         fun pp_tyvar_list symbol_list =
             pp_seq "* " ppTyvar symbol_list
       in
         case tb of
             Tb {tyc, def, tyvars} => pp_sym tyc
                                      ^  " ="
                                      ^ pp_tyvar_list tyvars
           | MarkTb (t, r) => ppTb t
       end

   and ppDb db =
       let
         fun pp_tyvar_list symbol_list =
             pp_seq ", " ppTyvar symbol_list
       in
         case db of
             Db {tyc, tyvars, rhs, lazyp} => pp_tyvar_list tyvars
                                             ^ pp_sym tyc
                                             ^  " = "
                                             ^ ppDbrhs rhs
           | MarkDb (t, r) => ppDb t
       end

   and ppDbrhs rhs =
       let
         fun pprhs (sym, tv) =
             case tv of
                 SOME a => pp_sym sym
                           ^ " of "
                           ^ pp_typ a
               | NONE => pp_sym sym
       in
         pp_seq " | " pprhs rhs
       end

   and ppEb eb =
       case eb of
           EbGen {exn, etype} =>
           (case etype of
                SOME a => pp_sym exn
                          ^ " = "
                          ^ pp_typ a
              | NONE => pp_sym exn)
         | EbDef {exn, edef} =>
           pp_sym exn
           ^ " = "
           ^ pp_symbol_list edef
         | MarkEb (t, r) => ppEb t


end
