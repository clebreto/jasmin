open Prog

val pp_list :
   ('a, 'b, 'c, 'd, 'd, 'a) CamlinternalFormatBasics.format6 ->
   (Format.formatter -> 'e -> unit) ->
   Format.formatter -> 'e list -> unit

val pp_bool : Format.formatter -> bool -> unit

val pp_iloc : Format.formatter -> i_loc -> unit
val pp_ptype : Format.formatter -> pty -> unit
val pp_plval : Format.formatter -> pty glval -> unit
val pp_pexpr : Format.formatter -> pexpr -> unit
val pp_pprog : Format.formatter -> 'info pprog -> unit

val pp_var   : debug:bool -> Format.formatter -> var -> unit

val pp_expr  : debug:bool -> Format.formatter -> expr -> unit

val pp_instr : debug:bool -> Format.formatter -> 'info instr -> unit

val pp_stmt  : debug:bool -> Format.formatter -> 'info stmt  -> unit

val pp_ifunc : debug:bool -> (Format.formatter -> 'info -> unit) ->
               Format.formatter -> 'info func -> unit

val pp_func  : debug:bool ->
               Format.formatter -> 'info func -> unit

val pp_iprog : debug:bool -> (Format.formatter -> 'info -> unit) ->
               Format.formatter -> 'info prog -> unit

val pp_prog  : debug:bool ->
               Format.formatter -> 'info prog -> unit

(* val pp_cprog : Format.formatter -> Expr.prog -> unit *)

