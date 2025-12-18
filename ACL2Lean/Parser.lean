import ACL2Lean.Syntax

namespace ACL2

namespace Parse

abbrev Stream := List Char

private def dropWhile (p : Char → Bool) : Stream → Stream
  | [] => []
  | c :: cs => if p c then dropWhile p cs else c :: cs

private def span (p : Char → Bool) : Stream → (List Char × Stream)
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (taken, rest) := span p cs
        (c :: taken, rest)
      else
        ([], c :: cs)

partial def skipWS : Stream → Stream
  | [] => []
  | c :: cs =>
      if c = ';' then
        skipWS (dropWhile (fun d => d ≠ '\n') cs)
      else if c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '\r' then
        skipWS cs
      else if c = '#' then
        match cs with
        | '|' :: rest =>
            let rec skipBlock : Nat → Stream → Stream
              | 0, r => skipWS r
              | _, [] => []
              | d, '#' :: '|' :: r => skipBlock (d + 1) r
              | d, '|' :: '#' :: r => skipBlock (d - 1) r
              | d, _ :: r => skipBlock d r
            skipBlock 1 rest
        | _ => c :: cs
      else
        c :: cs

private def readString : Stream → Except String (String × Stream)
  | [] => .error "unterminated string"
  | c :: cs =>
      if c = '"' then
        let rec go : List Char → Stream → Except String (String × Stream)
          | _, [] => .error "unterminated string"
          | acc, '"' :: rest => .ok (String.ofList (acc.reverse), rest)
          | acc, '\\' :: rest =>
              match rest with
              | [] => .error "unterminated escape"
              | h :: tl => go (h :: acc) tl
          | acc, h :: rest => go (h :: acc) rest
        go [] cs
      else
        .error "string literal must start with quote"

private def isAtomChar (c : Char) : Bool :=
  ¬ (c = '(' ∨ c = ')' ∨ c = ' ' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t')

private def readAtom (cs : Stream) : (String × Stream) :=
  let (tok, rest) := span isAtomChar cs
  (String.ofList tok, rest)

mutual
  partial def parseList (cs : Stream) (acc : List SExpr := [])
      : Except String (SExpr × Stream) :=
    let cs := skipWS cs
    match cs with
    | [] => .error "unterminated list"
    | ')' :: rest => .ok (SExpr.ofList acc.reverse, rest)
    | _ =>
        match parseSExpr cs with
        | .error e => .error e
        | .ok (sx, rest) => parseList rest (sx :: acc)

  partial def parseQuote (tag : String) (cs : Stream)
      : Except String (SExpr × Stream) :=
    match parseSExpr cs with
    | .error e => .error e
    | .ok (sx, rest) =>
        let sym := SExpr.atom (.symbol { name := tag })
        let quoted := SExpr.ofList [sym, sx]
        .ok (quoted, rest)

  partial def parseSExpr (input : Stream) : Except String (SExpr × Stream) :=
    let cs := skipWS input
    match cs with
    | [] => .error "unexpected end of file"
    | '(' :: rest => parseList rest
    | ')' :: _ => .error "unexpected )"
    | '\'' :: rest => parseQuote "quote" rest
    | '`' :: rest => parseQuote "quasiquote" rest
    | ',' :: '@' :: rest =>
        match parseSExpr rest with
        | .error e => .error e
        | .ok (sx, tail) =>
            let sym := SExpr.atom (.symbol { name := "unquote-splicing" })
            .ok (SExpr.ofList [sym, sx], tail)
    | ',' :: rest => parseQuote "unquote" rest
    | '"' :: _ =>
        match readString cs with
        | .error e => .error e
        | .ok (str, rest) =>
            .ok (SExpr.atom (.string str), rest)
    | '|' :: rest =>
        let rec go : List Char → Stream → Except String (String × Stream)
          | _, [] => .error "unterminated escaped symbol"
          | acc, '|' :: rest => .ok (String.ofList acc.reverse, rest)
          | acc, h :: rest => go (h :: acc) rest
        match go [] rest with
        | .error e => .error e
        | .ok (str, rest) => .ok (SExpr.atom (.symbol { name := str }), rest)
    | '#' :: '\\' :: rest =>
        let (tok, tail) := span isAtomChar rest
        let repr := "#\\" ++ String.ofList tok
        .ok (SExpr.atom (.symbol { name := repr }), tail)
    | '#' :: '+' :: rest =>
        match parseSExpr rest with
        | .error e => .error e
        | .ok (_, rest2) =>
            match parseSExpr rest2 with
            | .error e => .error e
            | .ok (_, rest3) => parseSExpr rest3
    | '#' :: '-' :: rest =>
        match parseSExpr rest with
        | .error e => .error e
        | .ok (_, rest2) => parseSExpr rest2
    | ':' :: _ =>
        let (tok, rest) := readAtom cs
        let kw := (tok.drop 1).toString
        .ok (SExpr.atom (.keyword kw), rest)
    | _ =>
        let (tok, rest) := readAtom cs
        let atom : Atom :=
          if tok = "t" then .bool true
          else if tok = "nil" then .bool false
          else
            match tok.toInt? with
            | some n => .number (.int n)
            | none =>
              if tok.contains '/' then
                let parts := tok.splitOn "/"
                match parts with
                | [numStr, denStr] =>
                    match numStr.toInt?, denStr.toNat? with
                    | some n, some d => .number (.rational n d)
                    | _, _ => .symbol { name := tok }
                | _ => .symbol { name := tok }
              else if tok.contains '.' then
                -- very crude decimal parsing
                .symbol { name := tok }
              else
                let parts := tok.splitOn "::"
                match parts with
                | [pkg, name] => .symbol { package := pkg, name }
                | _ => .symbol { name := tok }
        .ok (SExpr.atom atom, rest)
end

/-- Parse all s-expressions from a string. -/
partial def parseAll : String → Except String (List SExpr)
  | str =>
    let rec loop : Stream → List SExpr → Except String (List SExpr)
      | cs, acc =>
        let cs := skipWS cs
        match cs with
        | [] => .ok acc.reverse
        | ')' :: _ => .error "extra )"
        | _ =>
            match parseSExpr cs with
            | .error e => .error e
            | .ok (sx, rest) => loop rest (sx :: acc)
    loop str.toList []

end Parse

end ACL2
