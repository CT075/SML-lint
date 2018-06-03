
fun fgood x =
  case x of
       SOME y => SOME (y+1)
     | NONE => NONE

fun fbad x =
  if x = NONE then NONE else
  let val SOME y = x
  in SOME (y+1)
  end

