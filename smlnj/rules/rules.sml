structure Rules : RULES =
struct
  (* Outputted strings should be (error,hint) *)
  type viol_fmt = Ast.exp -> (string*string)
  type rule = (Ast.exp -> Ast.exp list) * viol_fmt

  (* Edit this variable to include rules! *)
  val enabled_rules =
    [
    ]
end

