import Lean

/-!
# KanLampe.Syntax.Rules

Port of `Lampe.Syntax.Rules`.  Declares the raw syntax categories
(`noir_expr`, `noir_type`, `noir_ident`, ...) and all corresponding
`syntax` rules used by the Noir DSL frontend.  This file is content-
identical to the upstream other than the namespace change.
-/

namespace KanLampe

declare_syntax_cat noir_const_num
declare_syntax_cat noir_expr
declare_syntax_cat noir_func_param
declare_syntax_cat noir_funcref
declare_syntax_cat noir_gen_def
declare_syntax_cat noir_gen_val
declare_syntax_cat noir_ident
declare_syntax_cat noir_kind
declare_syntax_cat noir_lam_param
declare_syntax_cat noir_lambda
declare_syntax_cat noir_lval
declare_syntax_cat noir_pat
declare_syntax_cat noir_top_level
declare_syntax_cat noir_type

syntax noir_arrow := "->" <|> "→"

syntax noir_depr? := ("[[" "deprecated" (ppSpace str)? "]]" ppSpace)?

syntax noir_alias := noir_ident "<" noir_gen_def,* ">" ":=" noir_type ";"

syntax noir_type_def := "<" noir_gen_def,* ">" "{"
  sepBy(noir_type, ",", ",", allowTrailingSep) "}"

syntax noir_trait_method := "method" noir_ident "<" noir_gen_def,* ">"
  "(" noir_type,* ")" noir_arrow noir_type

syntax noir_trait_def := noir_ident "<" noir_gen_def,* ">" "[" noir_gen_def,* "]" ":="
  "{" sepBy(noir_trait_method, ";", ";", allowTrailingSep) "}"

syntax noir_fn_def := noir_ident "<" noir_gen_def,* ">"
  "(" noir_func_param,* ")" noir_arrow noir_type ":=" noir_expr

syntax noir_where_clause := noir_type ":" noir_ident "<" noir_gen_val,* ">"

syntax noir_trait_impl_method := "noir_def" noir_fn_def

syntax noir_trait_impl := "<" noir_gen_def,* ">" noir_ident "<" noir_gen_val,* ">"
  "for" noir_type "where" "[" noir_where_clause,* "]" ":="
  "{" sepBy((noir_trait_impl_method), ";", ";", allowTrailingSep) "}"

syntax "_" : noir_ident
syntax ident : noir_ident
syntax ident "::" noir_ident : noir_ident

syntax ident : noir_type
syntax "String<" noir_gen_val ">" : noir_type
syntax "FmtString<" noir_gen_val "," noir_gen_val ">" : noir_type
syntax noir_ident "<" noir_gen_val,* ">" : noir_type
syntax "&" noir_type : noir_type
syntax "λ(" noir_type,* ")" ppSpace noir_arrow ppSpace noir_type : noir_type
syntax "_" : noir_type
syntax "@" noir_ident "<" noir_gen_val,* ">" : noir_type

syntax "Type" : noir_kind
syntax ident : noir_kind

syntax ident ":" noir_kind : noir_gen_def

syntax noir_type : noir_gen_val
syntax noir_const_num ":" noir_kind : noir_gen_val

syntax num : noir_const_num
syntax ident : noir_const_num
syntax "(" noir_const_num ")" : noir_const_num
syntax noir_const_num "+" noir_const_num : noir_const_num
syntax noir_const_num "-" noir_const_num : noir_const_num
syntax noir_const_num "*" noir_const_num : noir_const_num
syntax noir_const_num "/" noir_const_num : noir_const_num
syntax noir_const_num "%" noir_const_num : noir_const_num

syntax ident ppSpace ":" ppSpace noir_type : noir_func_param
syntax "mut" ident ":" noir_type : noir_func_param
syntax "_" ":" noir_type : noir_func_param

syntax ("-" noWs)? num ppSpace ":" ppSpace noir_type : noir_expr
syntax str : noir_expr
syntax "#_true" : noir_expr
syntax "#_false" : noir_expr
syntax "#_unit" : noir_expr

syntax "{" sepBy(ppLine noir_expr, ";", ";", allowTrailingSep) ppLine ppDedent("}") : noir_expr

syntax "#_skip" : noir_expr
syntax noir_ident : noir_expr
syntax "if" ppSpace noir_expr ppSpace "then" ppSpace noir_expr ppSpace ("else" ppSpace noir_expr)? : noir_expr
syntax noir_funcref "(" noir_expr,* ")" : noir_expr
syntax noir_lambda : noir_expr
syntax noir_funcref : noir_expr
syntax noir_expr "." num : noir_expr
syntax "uConst!(" ident ppSpace ":" ppSpace noir_kind ")" : noir_expr
syntax "fConst!(" ident ppSpace ":" ppSpace noir_kind ")" : noir_expr
syntax "(" noir_expr ")" : noir_expr
syntax "sorry" : noir_expr

syntax noir_lval ppSpace "=" ppSpace noir_expr : noir_expr
syntax "let" ppSpace noir_pat ppSpace "=" ppSpace noir_expr : noir_expr
syntax "for" ppSpace noir_ident ppSpace "in" ppSpace noir_expr ppSpace ".." ppSpace noir_expr ppSpace "do" ppSpace noir_expr : noir_expr

syntax "(" noir_ident ppSpace "as" ppSpace noir_type ")" : noir_funcref
syntax "(" noir_lambda ")" : noir_funcref
syntax "(" "#_" ident ppSpace "returning" ppSpace noir_type ")" : noir_funcref
syntax "(" noir_ident "<" noir_gen_val,* ">" ppSpace "as" ppSpace noir_type ")" : noir_funcref
syntax "(" "(" noir_type ppSpace "as" ppSpace noir_ident "<" noir_gen_val,* ">" ")"
  "::" noir_ident "<" noir_gen_val,* ">" ppSpace "as" ppSpace noir_type ")" : noir_funcref

syntax noir_pat ppSpace ":" ppSpace noir_type : noir_lam_param
syntax "fn" "(" noir_lam_param,* ")" ppSpace ":" ppSpace noir_type ppSpace ":=" ppSpace noir_expr : noir_lambda

syntax noir_ident : noir_pat
syntax "mut" ppSpace noir_ident : noir_pat
syntax "(" noir_pat,* ")" : noir_pat

syntax ident : noir_lval
syntax "(" noir_lval "." num ppSpace ":" ppSpace noir_type ")" : noir_lval
syntax "(" noir_lval "[" noir_expr "]" ppSpace ":" ppSpace noir_type ")" : noir_lval
syntax "(" noir_lval "[[" noir_expr "]]" ppSpace ":" ppSpace noir_type ")" : noir_lval
syntax "(" "*" noir_expr ":" noir_type ")" : noir_lval

syntax "splice!(" term ")" : noir_expr
syntax "splice!(" term ")" : noir_type

end KanLampe
