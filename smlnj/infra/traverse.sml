
signature MAPPABLE = sig
  type 'a t

  val fmap : ('a -> 'b) -> 'a t -> 'b t
end

functor MkTraverse(M: MAPPABLE) : TRAVERSE =
struct
  infix 2 <<<
  infix 2 >>>

  fun f <<< g = f o g
  fun f >>> g = g o f

  type 'a f = 'a M.t
  datatype t = Fix of t f

  val inj = Fix
  fun prj (Fix x) = x

  fun cata f = prj >>> M.fmap (cata f) >>> f
  fun ana f = inj <<< M.fmap (ana f) <<< f

  open Either

  fun para f =
    let fun fanout t = (t, para f t)
    in prj >>> M.fmap fanout >>> f
    end

  fun apo f =
    let
      fun fanin (INL a) = a
        | fanin (INR b) = apo f b
    in
      inj <<< M.fmap fanin <<< f
    end
end

