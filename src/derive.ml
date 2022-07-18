open Syntax

(* 推論規則を表す型 *)
type rule =
  | BPlus of judgement
  | BMinus of judgement
  | BTimes of judgement
  | BLt of judgement

let rec derive_exp = function
     |

   let derive_judgement = function
     | Eval (env, exp, value) -> derive_exp env exp value
     | PlusJ ->
