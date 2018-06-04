signature TRAVERSE = sig
  type 'a f
  datatype t = Fix of t f

  val inj : t f -> t
  val prj : t -> t f

  val cata : ('a f -> 'a) -> t -> 'a
  val ana : ('a -> 'a f) -> 'a -> t
end

