Control.Elab.unusedBindingWarn := false;

signature LINT =
sig
  val parseFile : string -> Ast.dec
  val pp_pat : Ast.pat -> string
  val pp_exp : Ast.exp -> bool -> string
end

structure Lint : LINT =
struct
   open Ast

   fun parseFile filename =
       let
         val stream = TextIO.openIn filename
         val interactive = false
         val consumer = ErrorMsg.defaultConsumer ()
         val source = Source.newSource (filename, stream, interactive, consumer)
       in
         SmlFile.parse source
       end

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

   (* FIX *)
   fun isTUPLEpat _ = false
   fun isTUPLEexp _ = false

   fun stripMark (MarkExp(a,_)) = stripMark a
     | stripMark x = x

   fun pp_sym s = Symbol.name s

   fun pp_symbol_list symbols =
       pp_seq "." pp_sym symbols


   fun pp_typ _ = raise Fail "Unimplemented"

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
                                                  ^ " :"
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



   fun pp_exp exp atom =
       case exp of
           VarExp p => pp_symbol_list p
         | FnExp rules =>
           "fn " ^ (pp_seq " | " pp_rule rules)
         | FlatAppExp fap =>
           pp_seq " " (fn {item, fixity, region} => pp_exp item true) fap
         | AppExp e => (lpcond atom)
                       ^ pp_app_exp (AppExp e, 0,0 (*nullFix, nullFix*))
                       ^ (rpcond atom)
         | CaseExp {expr, rules} =>
           "(case "
           ^ pp_exp expr true
           ^ "of \n"
           ^ (pp_seq "\n | " pp_rule rules)
           ^ ")"
         | LetExp {dec, expr} =>
           " let\n"
           ^ pp_dec dec
           ^ "\n in\n"
           ^ pp_exp expr false
           ^ "\n end"
         | SeqExp exps =>
           let
             fun parenThunk () =
                 "("
                 ^ pp_seq ";" (fn exp => pp_exp exp false) exps
                 ^ ")"
             fun subExpCount (MarkExp (expr, _)) = subExpCount expr
               | subExpCount (FlatAppExp subexps) = length subexps
               | subExpCount _ = 1
           in
             case exps
              of [expr] => if (subExpCount expr) < 2
                           then pp_exp expr false
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
                ^ pp_seq "," (fn (_, exp) => pp_exp exp false) fields
                ^ ")"
           else "{"
                ^ pp_seq "," (fn (name, exp) => (pp_sym name) ^ "=" ^ pp_exp exp false) fields
                ^ "}"
         | ListExp p => "["
                        ^ pp_seq "," (fn exp => pp_exp exp false) p
                        ^ "]"
         | TupleExp p => "("
                         ^ pp_seq "," (fn exp => pp_exp exp false) p
                         ^ ")"
         | SelectorExp name =>
           lpcond atom
           ^ "#"
           ^ pp_sym name
           ^ rpcond atom
         | ConstraintExp {expr, constraint} =>
           lpcond atom
           ^ pp_exp expr false
           ^ ":"
           ^ pp_typ constraint
           ^ rpcond atom
         | HandleExp {expr, rules} =>
           lpcond atom
           ^ pp_exp expr atom
           ^ "handle "
           ^ pp_seq "| " pp_rule rules
           ^ rpcond atom
         | RaiseExp exp =>
           lpcond atom
           ^ "raise "
           ^ pp_exp exp true
           ^ rpcond atom
         | IfExp {test, thenCase, elseCase} =>
           lpcond atom
           ^ "if "
           ^ pp_exp test false
           ^ "then "
           ^ pp_exp thenCase false
           ^ "else "
           ^ pp_exp elseCase false
           ^ rpcond atom
         | AndalsoExp (e1, e2) =>
           lpcond atom
           ^ pp_exp e1 true
           ^ "andalso "
           ^ pp_exp e2 true
           ^ rpcond atom
         | OrelseExp (e1, e2) =>
           lpcond atom
           ^ pp_exp e1 true
           ^ "orelse "
           ^ pp_exp e2 true
           ^ rpcond atom
         | WhileExp {test, expr} =>
           "while "
           ^ pp_exp test false
           ^ "do "
           ^ pp_exp expr false
         | VectorExp [] => "#[]"
         | VectorExp exps =>
           "#["
           ^ pp_seq "," (fn exp => pp_exp exp false) exps
           ^ "]"
         | MarkExp (exp, (s, e)) =>
           (* If we want to modify a file in place, then the
            * source location information will be useful, so
            * we'll want to change this *)
           pp_exp exp atom

   and pp_app_exp (exp, left, right) =
       let
         (*
      fun fixitypp(name, rand, leftFix, rightFix) =
          let
            val dname = SymPath.toString (SymPath.SPATH name)
            val thisFix = case name of
                              [id] => lookFIX (env, id)
                            | _ => NONfix
            fun prNon exp = pp_exp exp true
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
                                  ^ pp_app_exp (pl, left, thisFix)
                                  ^ " " ^ dname ^ " "
                                  ^ pp_app_exp (pr, thisFix, right)
                                  ^ rpcond atom
                                end
                              | e' => prNon e')
              | NONfix => prNon rand
          end
         *)
         fun appPrint (AppExp {function=rator, argument=rand}, l, r) =
             (case stripMark rator of
                  (*  VarExp v => fixitypp (v, rand, l, r)
             |*)  rator => (pp_exp rator true) ^ " " ^ (pp_exp rand true))
           | appPrint (MarkExp (exp, (s, e)), l, r) =
             (* If we want to modify a file in place, then the
              * source location information will be useful, so
              * we'll want to change this *)
             appPrint (exp, l, r)
       in
         appPrint (exp, left, right)
       end

   and pp_rule (Rule {pat, exp}) =
       pp_pat pat
       ^ " => "
       ^ pp_exp exp false

   and pp_dec _ = raise Fail "Unimplemented"

end
