
signature AST_UTIL = sig
  structure A : AST
  include AST_EXT

  datatype uexpr = Unify of exp * uexpr expF

  val prj : uexpr -> (exp * uexpr expF)
  val inj : (exp * uexpr expF) -> uexpr

  val Out : uexpr -> exp
  val Into : exp -> uexpr
end

