(* 

THE PLAN!!!

1. Develop mutually recursive languages with FFI interfaces into each other (complete)
2. "Break" the mutual recursion, so that one language can be defined without the other
  Mutual recursion can be rewritten as an indexed inductive data type
  One approach: Read "The gentle art of levitation"
  Another approach: Post on coq-club describing the problem and see if someone knows what to do
3. ???
4. PROFIT!!!

*)

Inductive lang :=
  | A : lang
  | B : lang.

Inductive aExp : Set :=
  | Anat : nat -> aExp
  | AB : bExp -> aExp
with bExp : Set :=
  | Bnat : nat -> bExp
  | BA : aExp -> bExp.

Definition langExp (l : lang) : Set :=
  match l with
  | A => aExp
  | B => bExp
  end.

Inductive aC : lang -> Set :=
  | aC_hole : aC A
  | aC_AB : forall l, bC l -> aC l
with bC : lang -> Set :=
  | bC_hole : bC B
  | bC_BA : forall l, aC l -> bC l.

Definition langC (l : lang) : lang -> Set :=
  match l with
  | A => aC
  | B => bC
  end.

(*
Inductive X : bool -> Set :=
  | XT : X true
  | XF : X false
  | Xi : forall b, X b -> X b.
Definition f b (x : X b) : X b :=
  match x with
  | XT => XT
  | XF => XF
  | Xi b' x => Xi b' x
  end.
*)

Fixpoint aPlug (l : lang) (e : langExp l) (C : aC l) : aExp :=
  (match C in (aC l') return (langExp l' -> aExp) with
  | aC_hole => fun e' => e'
  | aC_AB l' bC => fun e' => AB (bPlug l' e' bC)
  end) e
with bPlug (l : lang) (e : langExp l) (C : bC l) : bExp :=
  (match C in (bC l') return (langExp l' -> bExp) with
  | bC_hole => fun e' => e'
  | bC_BA l' aC => fun e' => BA (aPlug l' e' aC)
  end) e.

Definition langPlug (l : lang) :=
  match l as l' return (forall l'', langExp l'' -> langC l' l'' -> langExp l') with
    | A => aPlug
    | B => bPlug
  end.

Inductive aT : aExp -> aExp -> Prop :=
  | aT_border : forall e, aT (AB (BA e)) e.

Inductive bT : bExp -> bExp -> Prop :=
  | bT_border : forall e, bT (BA (AB e)) e.

Definition langT (l : lang) :=
  match l as l' return langExp l' -> langExp l' -> Prop with
    | A => aT
    | B => bT
  end.

Inductive G (l : lang) : langExp l -> langExp l -> Prop :=
  | G_lift : forall l' (e e' : langExp l') (C : langC l l'), langT l' e e' -> G l (langPlug l l' e C) (langPlug l l' e' C).


(* ------------------ >8 --------------------- *)

(* with bT : bExp -> bExp -> Prop *)

(*with bPlug (e : bExp) (C : bC)*)

Section target.

Variable (I : Set).
Variable (I_C : Set).
Variable (I_plug : I -> I_C -> I).
Variable (I_red : I -> I -> Prop).

Inductive T_exp : Set :=
  | T_exp_bool : bool -> T_exp
  | T_exp_if : T_exp -> T_exp -> T_exp -> T_exp
  | T_exp_border : I -> T_exp.

Inductive T_C : Set :=
  | T_C_hole : T_C
  | T_C_if : T_C -> T_exp -> T_exp -> T_C
  | T_C_border : I_C -> T_C.

Fixpoint T_plug (e : T_exp) (cxt : T_C) :=
  match cxt with
    | T_C_hole => e
    | T_C_if cxt e1 e2 => T_exp_if (T_plug e cxt) e1 e2
    | T_C_border : 
  end.

Inductive T : T_exp -> T_exp -> Prop :=
  | T_IfTrue : forall e1 e2, T (T_exp_if (T_exp_bool true) e1 e2) e1
  | T_IfFalse : forall e1 e2, T (T_exp_if (T_exp_bool false) e1 e2) e2.

Inductive T_G : T_exp -> T_exp -> Prop :=
  | T_G_lift : forall e1 e2 C (* this needs to be parametric *), T e1 e2 -> T_G (T_plug e1 C) (T_plug e2 C).

End target.

Section ifc.

Inductive iexp :=
  
