
structure NestedIfs =
struct
  structure R = RuleUtil
  open ASTUtil
  open T

  infix 0 $
  fun f $ x = f x

  val NESTING_LIMIT = 2

  fun checkLevel (IfExpF {test=_,thenCase=d1,elseCase=d2}) =
        Int.max(d1, d2) + 1
    | checkLevel (CaseExpF {expr=_, rules=rl}) =
        foldl Int.max 0 (R.extractRuleF rl) + 1
    | checkLevel _ = 0
end

