signature AST_FUNC = sig
  structure A : AST

  include AST_EXT
  structure M : MAPPABLE where type 'a t = 'a expF

  type expr
  structure T : TRAVERSE where type t = expr

  val intoF : A.exp -> A.exp expF
  val into : A.exp -> expr
  val out : expr -> A.exp
  val outF : A.exp expF -> A.exp
end

