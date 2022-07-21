open Syntax

(* パターンと値を受け取り、それらがマッチするかを判定する関数 *)
let rec judge_match p v =
  match (p, v) with
  | VarPat x, _ -> MatchJ (p, v, ConsEnv (Empty, x, v))
  | NilPat, NilV -> MatchJ (p, v, Empty)
  | ConsPat (p1, p2), ConsV (v1, v2) -> (
      let m1 = judge_match p1 v1 in
      let m2 = judge_match p2 v2 in
      match (m1, m2) with
      | MatchJ (_, _, env1), MatchJ (_, _, env2) ->
          MatchJ (p, v, append_env env1 env2)
      | _ -> NotMatchJ (p, v))
  | Wild, _ -> MatchJ (Wild, v, Empty)
  | _ -> NotMatchJ (p, v)
