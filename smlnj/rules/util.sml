
structure RuleUtil =
struct
  structure A = Ast
  open ASTUtil

  fun extractRuleF rl = List.map (fn (RuleF {pat=_,exp=e}) => e) rl
end

