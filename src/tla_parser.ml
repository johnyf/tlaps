(*
 * parser.ml --- TLA+ parser
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** TLA+ parsing setup. The actual parsers are distributed in the
    following individual modules: {ul
    {- {!Expr.Parser}}
    {- {!Proof.Parser}}
    {- {!Module.Parser}}} *)

Revision.f "$Rev: 30204 $";;

open Ext

(** TLA+ tokens *)
module Token = struct

  type token_ =
    | BOF                               (* beginning of file *)
    | ID of string                      (* identifiers *)
    | OP of string                      (* operators *)
    | KWD of string                     (* keywords *)
    | NUM of string * string            (* numbers *)
    | STR of string                     (* strings *)
    | PUNCT of string                   (* misc. punctuation *)
    | ST of [`Star | `Plus | `Num of int] * string * int
                                        (* step token *)

  and token = { form : token_ ;
                mutable rep : string ;
                loc  : Loc.locus }

  let locus t = t.loc

  let bof loc = { form = BOF ; rep = "start of file" ; loc = loc }

  let rep t = match t.rep with
    | "" ->
        let trep = begin match t.form with
          | BOF -> "start of file"
          | ID x -> "identifier " ^ x
          | KWD x -> "keyword " ^ x
          | OP x -> "operator " ^ x
          | PUNCT x -> x
          | NUM (m, "") -> m
          | NUM (m, n) -> m ^ "." ^ n
          | STR s -> "\"" ^ s ^ "\""
          | ST (`Star, sl, ds) -> "<*>" ^ sl ^ String.make ds '.'
          | ST (`Plus, sl, ds) -> "<+>" ^ sl ^ String.make ds '.'
          | ST (`Num m, sl, ds) -> "<" ^ string_of_int m ^ ">" ^ sl ^ String.make ds '.'
        end in
        t.rep <- trep ;
        trep
    | rep -> rep

  let eq s t = s.form = t.form

  let pp_print_token ff t =
    Format.pp_print_string ff (rep t)

end

(** TLA+ precedence *)
module Prec = struct

  (** A precedence is a range of values. Invariant: the first
      component must be less than or equal to the second component. *)
  type prec = int * int

  (** Check that the first precedence range is completely below the
      second range. *)
  let below (a, b) (c, d) = b < c

  (** Check if the two given precedence ranges overlap. *)
  let conflict (a, b) (c, d) =
    (a <= c && c <= b) || (c <= a && a <= d)
end

module Fu = Fmtutil.Minimal (Prec)

module P = Pars.Pco.Make (Token) (Prec)

open P

(** The [pcx] is the state carried by the parsers. The [ledge] field
    contains the left edge of the active rectangle of input. *)
type pcx = {
  ledge : int ;
  clean : bool ;
}

let init = { ledge = -1 ; clean = true }

type 'a prs = (pcx, 'a) P.prs
type 'a lprs = 'a prs Lazy.t

let locate p =
  withloc p <$> begin
    fun (a, loc) -> Util.set_locus (Property.noprops a) loc
  end

let scan ts =
  get >>= fun px ->
    P.scan begin
      fun t ->
        if px.ledge <= Loc.column t.Token.loc.Loc.start then ts t.Token.form
        else None
    end

open Token

let punct p = scan begin
  function
    | PUNCT q when q = p -> Some p
    | _ -> None
end

let kwd k = scan begin
  fun tok ->
    match tok with
      | KWD j when j = k -> Some k
      | _ -> None
end

module Op = Optable

let anyinfix = scan begin
  function
    | OP p ->
        let rec loop = function
          | [] -> None
          | ({ Op.fix = Op.Infix _ } as top) :: _ -> Some (top.Op.name)
          | _ :: tops -> loop tops
        in loop (Hashtbl.find_all Op.optable p)
    | _ -> None
end

let infix o = anyinfix <?> (fun p -> o = p)

let anyprefix = scan begin
  function
    | OP p ->
        let rec loop = function
          | [] -> None
          | ({ Op.fix = Op.Prefix } as top) :: _ -> Some (top.Op.name)
          | _ :: tops -> loop tops
        in loop (Hashtbl.find_all Op.optable p)
    | _ -> None
end

let prefix o = anyprefix <?> (fun p -> o = p)

let anypostfix = scan begin
  function
    | OP p ->
        let rec loop = function
          | [] -> None
          | ({ Op.fix = Op.Postfix } as top) :: _ -> Some (top.Op.name)
          | _ :: tops -> loop tops
        in loop (Hashtbl.find_all Op.optable p)
    | _ -> None
end

let anyop = scan begin
  function
    | OP o ->
        let op = Hashtbl.find Optable.optable o in
          Some op.Optable.name
    | _ -> None
end

let anyident = scan begin
  function
    | ID i -> Some i
    | _ -> None
end

let ident i = anyident <?> (fun j -> i = j)

let anyname = scan begin
  function
    | ID nm | KWD nm -> Some nm
    | _ -> None
end

let number = scan begin
  function
    | NUM (m, n) -> Some (m, n)
    | _ -> None
end

let nat = scan begin
  function
    | NUM (m, "") -> Some (int_of_string m)
    | _ -> None
end

let str = scan begin
  function
    | STR (s) -> Some (s)
    | _ -> None
end

let pragma p = punct "(*{" >>> p <<< punct "}*)"

let pickle =
  let optable = Hashtbl.create 109 in
  let () =
    List.iter (fun (syns, rep) -> List.iter (fun syn -> Hashtbl.add optable syn rep) syns)
      [ [ "-." ],                  "a'uminus" ;
        [ "^+" ],                  "a'caretplus" ;
        [ "^*" ],                  "a'caretstar" ;
        [ "^#" ],                  "a'carethash" ;
        [ "-|" ],                  "a'dashvert" ;
        [ "::=" ],                 "a'coloncoloneq" ;
        [ ":=" ],                  "a'coloneq" ;
        [ "<" ],                   "a'lt" ;
        [ "=|" ],                  "a'eqvert" ;
        [ ">" ],                   "a'gt" ;
        [ "\\approx" ],            "a'approx" ;
        [ "\\asymp" ],             "a'asymp" ;
        [ "\\cong" ],              "a'cong" ;
        [ "\\doteq" ],             "a'doteq" ;
        [ "\\geq" ; ">=" ],        "a'gteq" ;
        [ "\\gg" ],                "a'gtgt" ;
        [ "<=" ; "=<" ; "\\leq" ], "a'lteq" ;
        [ "\\ll" ],                "a'ltlt" ;
        [ "\\prec" ],              "a'prec" ;
        [ "\\preceq" ],            "a'preceq" ;
        [ "\\propto" ],            "a'propto" ;
        [ "\\sim" ],               "a'sim" ;
        [ "\\simeq" ],             "a'simeq" ;
        [ "\\succ" ],              "a'succ" ;
        [ "\\succeq" ],            "a'succeq" ;
        [ "\\sqsubset" ],          "a'sqsubset" ;
        [ "\\sqsubseteq" ],        "a'sqsubseteq" ;
        [ "\\sqsupset" ],          "a'sqsupset" ;
        [ "\\sqsupseteq" ],        "a'sqsupseteq" ;
        [ "\\subset" ],            "a'subset" ;
        [ "\\supset" ],            "a'supset" ;
        [ "\\supseteq" ],          "a'supseteq" ;
        [ "|-" ],                  "a'vertdash" ;
        [ "|=" ],                  "a'verteq" ;
        [ "@@" ],                  "a'atat" ;
        [ ":>" ],                  "a'colongt" ;
        [ "<:" ],                  "a'ltcolon" ;
        [ ".." ],                  "a'dotdot" ;
        [ "..." ],                 "a'dotdotdot" ;
        [ "!!" ],                  "a'bangbang" ;
        [ "##" ],                  "a'hashhash" ;
        [ "$" ],                   "a'dollar" ;
        [ "$$" ],                  "a'dollardollar" ;
        [ "??" ],                  "a'qmqm" ;
        [ "\\sqcap" ],             "a'sqcap" ;
        [ "\\sqcup" ],             "a'sqcup" ;
        [ "\\uplus" ],             "a'uplus" ;
        [ "\\wr" ],                "a'wr" ;
        [ "(+)" ; "\\oplus" ],     "a'oplus" ;
        [ "+" ],                   "a'plus" ;
        [ "-" ],                   "a'minus" ;
        [ "++" ],                  "a'plusplus" ;
        [ "%" ],                   "a'pc" ;
        [ "%%" ],                  "a'pcpc" ;
        [ "|" ],                   "a'vert" ;
        [ "||" ],                  "a'vertvert" ;
        [ "\\X" ; "\\times" ],     "a'x" ;
        [ "(-)" ; "\\ominus" ],    "a'ominus" ;
        [ "--" ],                  "a'minusminus" ;
        [ "&" ],                   "a'and" ;
        [ "&&" ],                  "a'andand" ;
        [ "(.)" ; "\\odot" ],      "a'odot" ;
        [ "(/)" ; "\\oslash" ],    "a'oslash" ;
        [ "(\\X)" ; "\\otimes" ],  "a'otimes" ;
        [ "*" ],                   "a'ast" ;
        [ "**" ],                  "a'astast" ;
        [ "/" ],                   "a'slash" ;
        [ "//" ],                  "a'slashslash" ;
        [ "\\bigcirc" ],           "a'bigcirc" ;
        [ "\\bullet" ],            "a'bullet" ;
        [ "\\div" ],               "a'div" ;
        [ "\\o" ; "\\circ" ],      "a'circ" ;
        [ "\\star" ],              "a'star" ;
        [ "^" ],                   "a'caret" ;
        [ "^^" ],                  "a'caretcaret" ;
        [ "[]" ],                  "a'box" ;
        [ "<>" ],                  "a'diamond" ;
        [ "-+->" ],                "a'actplus" ;
        [ "\\cdot" ],              "a'cdot" ;
        [ "'" ],                   "a'prime" ;
      ] in
  let module SS = Set.Make (String) in
  let tla_keys = [
      (* Isabelle/TLA+ types and definitions -- see tools/all_defs.sml *)
      "All"; "Append"; (* "BOOLEAN"; *) "Bijections"; "Case";
      "CaseArm"; "CaseOther"; "Char"; "Choice"; (* "DOMAIN"; *)
      "EnumFuncSet"; "Ex"; (* "FALSE"; *) "Fcn"; "FuncSet"; "INTER";
      "Id"; "Image"; "Injections"; "Injective"; "InjectiveOn"; "Int";
      "Inverse"; "Len"; "Let"; "Monotonic"; "Nat"; "Nibble"; "Not";
      "PeanoAxioms"; "Pred"; "Product"; "Range"; (* "SUBSET"; *)
      "Seq"; "String"; "Succ"; "Surjections"; "Surjective";
      (* "TRUE"; *) "TYPE"; "Trueprop"; (* "UNION"; *) "Zero"; "abs";
      "addElt"; "addnat"; "all"; "antisymmetric"; "any"; "aprop";
      "arbitrary"; "args"; "arith_add"; "asms"; "bAll"; "bChoice";
      "bEx"; "boolify"; "c"; "cap"; "cargs"; "case_arm"; "case_arms";
      "cases_conj"; "cases_equal"; "cases_forall"; "cases_implies";
      "char"; "cidts"; "classes"; "cond"; "conj"; "conjunction";
      "converse"; "cs"; "cup"; "default"; "diff"; "diffnat"; "disj";
      "div"; "divmodNat"; "divmod_rel"; "domrng"; "domrngs"; "dummy";
      "dummy_pattern"; "dvd"; "emptySeq"; "eq"; "equivalence";
      "except"; "extend"; "fapply"; "float_const"; "float_token";
      "fun"; "geq"; "gfp"; "greater"; "id"; "idt"; "idts"; "iff";
      "imp"; "in"; "index"; "infinity"; "irreflexive"; "isAFcn";
      "isASeq"; "isBool"; "isNeg"; "isPos"; "itself"; "leq"; "less";
      "letbind"; "letbinds"; "lfp"; "logic"; "longid"; "minus";
      "mod"; "mult"; "multnat"; "natInterval"; "num"; "num_const";
      "oneArg"; "prod"; "prop"; "psubset"; "psupset"; "pttrn";
      "pttrns"; "reflexive"; "rel_comp"; "rel_domain"; "rel_image";
      "rel_range"; "setOfAll"; "setOfPairs"; "setminus"; "sgn";
      "sort"; "sort_constraint"; "struct"; "subsetOf"; "subseteq";
      "symmetric"; "term"; "tid"; "tpl"; "transitive"; "tvar";
      "type"; "types"; "upair"; "upto"; "var"; "xcpt"; "xnum";
      "xstr";
    ]
  in
  let idtable =
    List.fold_left begin
      fun sks s -> SS.add s sks
    end SS.empty (tla_keys @ Isabelle_keywords.v)
  in
  (* special tokens that are apparently illegal *)
  let idtable = SS.add "O" idtable in
  fun id ->
    let id = String.copy id in
    for i = 0 to String.length id - 1 do
      if id.[i] = '!' then id.[i] <- '\''
    done ;
    if Hashtbl.mem optable id then Hashtbl.find optable id
    else
      let id0 = Char.code (id.[0]) in
      if id0 = Char.code '_'
        || (Char.code '0' <= id0 && id0 <= Char.code '9')
        || SS.mem id idtable
      then "a'" ^ id
      else id
