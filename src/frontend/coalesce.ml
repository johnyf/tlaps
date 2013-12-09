(*
 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 32093 $";;

open Ext
open Format
open Tla_parser
open Property

open Expr.T
open Expr.Subst

let coalesce_fol e = e
