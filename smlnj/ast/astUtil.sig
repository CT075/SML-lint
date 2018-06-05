signature AST_UTIL = sig
  structure A : AST

  include AST_EXT

  type expr
  include TRAVERSE where type t = expr

  val into : A.exp -> expr
  val out : expr -> A.exp
end

