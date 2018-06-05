
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

  infix 3 &&&
  fun f &&& g = fn x => (f x, g x)

  fun fst (x,y) = x
  fun snd (x,y) = y

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

  fun mutu f g = snd <<< cata (f &&& g)
  fun zygo f g = mutu (f o M.fmap fst) g
end

