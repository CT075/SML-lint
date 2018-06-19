
structure ASTUtil : AST_UTIL =
struct
  structure AF = ASTFunc
  open ASTFunc

  infix 3 &&&
  fun f &&& g = fn x => (f x, g x)

  infix 2 <<<
  infix 2 >>>

  fun f <<< g = f o g
  fun f >>> g = g o f

  fun fst (x,y) = x
  fun snd (x,y) = y
  fun first f (x,y) = (f x, y)
  fun second f (x,y) = (x, f y)

  datatype uexpr = Unify of AF.exp * uexpr expF

  fun prj (Unify p) = p
  val inj = Unify

  fun build f = inj <<< second (M.fmap (build f)) <<< (Fn.id &&& f)

  (* Originally, "build" and "teardown" were named "Ana" and "Cata", but I
   * felt that those were misleading..
   *)
  fun teardown (f: (AF.exp * 'a expF) -> 'a) : uexpr -> 'a =
    prj >>> second (M.fmap (teardown f)) >>> f

  fun Out (Unify (x,_)) = x
  fun Into a = build intoF a

  fun collapseVia
      (f: (AF.exp * 'a expF) -> 'a)
      (g: (AF.exp * ('a * 'b) expF) -> 'b)
      : uexpr -> 'b =
    snd <<< teardown ((f o second (M.fmap fst)) &&& g)
end

