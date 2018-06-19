
signature AST_UTIL = sig
  structure A : AST
  include AST_EXT

  datatype uexpr = Unify of exp * uexpr expF

  val prj : uexpr -> (exp * uexpr expF)
  val inj : (exp * uexpr expF) -> uexpr

  val Out : uexpr -> exp
  val Into : exp -> uexpr

  val build : (A.exp -> A.exp expF) -> A.exp -> uexpr
  val teardown : (A.exp * 'a expF -> 'a) -> uexpr -> 'a

  val collapseVia :
    (A.exp * 'a expF -> 'a) ->
    (A.exp * ('a*'b) expF -> 'b) ->
    uexpr -> 'b
end

