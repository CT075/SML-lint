signature TRAVERSE = sig
  type 'a f
  datatype t = Fix of t f

  val inj : t f -> t
  val prj : t -> t f

  val cata : ('a f -> 'a) -> t -> 'a
  val ana : ('a -> 'a f) -> 'a -> t

  val para : ((t * 'a) f -> 'a) -> t -> 'a
  val apo : ('a -> ((t, 'a) Either.either) f) -> 'a -> t

  val zygo : ('a f -> 'a) -> (('a*'b) f -> 'b) -> t -> 'b
  val mutu : (('a*'b) f -> 'a) -> (('a*'b) f -> 'b) -> t -> 'b
end

