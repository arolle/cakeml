(*
 * example of acyclic theory
 *)
open preamble setSpecTheory holSyntaxLibTheory holSyntaxTheory
     holSyntaxExtraTheory holBoolSyntaxTheory holAxiomsSyntaxTheory
     holExtensionTheory holBoolTheory holSyntaxCyclicityTheory

val _ = new_theory"holSyntaxCyclicityExample";

Overload Fun = ``λs t. Tyapp «fun» [s;t]``
Overload Bool = ``Tyapp «bool» []``

Definition dep_def:
  dep = [
  (INL (Fun (Tyvar «A» ) (Tyvar «B» )),INL (Tyvar «A» ));
  (INL (Fun (Tyvar «A» ) (Tyvar «B» )),INL (Tyvar «B» ));
  (INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INL (Tyvar «A» ));
  (INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)),INR (Const «T» Bool));
  (INR (Const «/\\» (Fun Bool (Fun Bool Bool))),INR (Const «T» Bool));
  (INR (Const «==>» (Fun Bool (Fun Bool Bool))), INR (Const «/\\» (Fun Bool (Fun Bool Bool))));
  (INR (Const «=» (Fun (Tyvar «A» ) (Fun (Tyvar «A» ) Bool)) ),INL (Tyvar «A» ));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INL (Tyvar «A» ));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INR (Const «!» (Fun (Fun Bool Bool) Bool)));
  (INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «@» (Fun (Fun (Tyvar «A» ) Bool) (Tyvar «A» )) ),INL (Tyvar «A» ));
  (INR (Const «F» Bool),INR (Const «!» (Fun (Fun Bool Bool) Bool)));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «A» ));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «B» ));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «!» (Fun (Fun (Tyvar «A» ) Bool) Bool)));
  (INR (Const «ONE_ONE» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «A»));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INL (Tyvar «B»));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «!» (Fun (Fun (Tyvar «B» ) Bool) Bool)));
  (INR (Const «ONTO» (Fun (Fun (Tyvar «A» ) (Tyvar «B» )) Bool)), INR (Const «?» (Fun (Fun (Tyvar «A» ) Bool) Bool)));
  (INR (Const «\\/» (Fun Bool (Fun Bool Bool))), INR (Const «!» (Fun (Fun Bool Bool) Bool)));
  (INR (Const «\\/» (Fun Bool (Fun Bool Bool))), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «~» (Fun Bool Bool)), INR (Const «==>» (Fun Bool (Fun Bool Bool))));
  (INR (Const «~» (Fun Bool Bool)),INR (Const «F» Bool))
  ]
End

Theorem dependency_hol_ctxt_eq:
  set (MAP ((λf. (f ## f)) (LR_TYPE_SUBST [(Tyvar «B», Tyvar «aa»);(Tyvar «A»,Tyvar «a»)]))
  (dependency_compute hol_ctxt)) = set dep
Proof
  fs[dependency_compute_def,hol_ctxt_def,dependency_cases,mk_infinity_ctxt_def,
    mk_bool_ctxt_def,mk_eta_ctxt_def,mk_select_ctxt_def,finite_hol_ctxt_def,
    init_ctxt_def,TrueDef_def,wellformed_compute_def,allCInsts_def,typeof_def,
    equation_def,ImpliesDef_def,is_fun_def,REPLICATE,Excl"TYPE_SUBST_def",
    TrueDef_def,AndDef_def,ForallDef_def,ExistsDef_def,FalseDef_def,NotDef_def,
    cj 2 TYPE_SUBST_def,cj 2 $ GSYM is_instance_simps,PULL_EXISTS,PAIR_MAP]
  >> EVAL_TAC
  >> fs[cj 2 TYPE_SUBST_def,cj 2 $ GSYM is_instance_simps,Excl"TYPE_SUBST_def",LR_TYPE_SUBST_cases]
  >> EVAL_TAC
QED

Theorem dependency_hol_ctxt_eq =
  REWRITE_RULE[dep_def] dependency_hol_ctxt_eq

(*
cyclic p dep dep' = dep''
==> cyclic (SUC p) dep dep' = cyclic p dep dep''

val dep' = EVAL ``OUTR $ THE $ cyclic 0 dep dep`` |> concl |> rand
val dep' = EVAL ``OUTR $ THE $ cyclic 1 dep ^(dep')`` |> concl |> rand
(* cyclic 2 = *)
val dep' = EVAL ``OUTR $ THE $ cyclic 1 dep ^(dep')`` |> concl |> rand
(* cyclic 3 = *)
val dep' = EVAL ``OUTR $ THE $ cyclic 1 dep ^(dep')`` |> concl |> rand

EVAL ``cyclic 4 dep dep``
*)

val _ = export_theory();
