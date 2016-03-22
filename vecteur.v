(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export Classical.
Require Export Field_affine.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition vec (A B : PO) := add_PP (cons (-1) A) (cons 1 B).
 
Ltac Ringvec := unfold vec in |- *; RingPP.
 
Ltac Fieldvec k := unfold vec in |- *; FieldPP k.
 
Ltac contrapose H :=
  match goal with
  | h:(~ _) |- (~ _) => red in |- *; intros; apply h
  end.
 
Lemma Chasles_vec : forall A B C : PO, add_PP (vec A B) (vec B C) = vec A C.
intros; Ringvec.
Qed.
 
Lemma opp_vecteur : forall A B : PO, vec B A = mult_PP (-1) (vec A B).
intros; Ringvec.
Qed.
 
Lemma egalite_vecteur :
 forall A B C D : PO, vec A B = vec C D -> vec A C = vec B D.
unfold vec in |- *; intros.
RingPP1 H.
RingPP.
Qed.
Hint Resolve egalite_vecteur: geo.
 
Definition parallelogramme (A B C D : PO) := vec A B = vec D C.
Hint Unfold parallelogramme: geo.
 
Lemma parallelogramme_ordre_cycle :
 forall A B C D : PO, parallelogramme A B C D -> parallelogramme B C D A.
unfold parallelogramme in |- *; intros.
symmetry  in |- *; auto with geo.
Qed.
 
Lemma parallelogramme_ordre_permute :
 forall A B C D : PO, parallelogramme A B C D -> parallelogramme A D C B.
unfold parallelogramme in |- *; intros.
auto with geo.
Qed.
Hint Immediate parallelogramme_ordre_permute: geo.
Hint Resolve parallelogramme_ordre_cycle: geo.
 
Lemma add_PP_vecteur :
 forall (a b : R) (A B C M : PO),
 a + b <> 0 ->
 add_PP (cons a A) (cons b B) = cons (a + b) C ->
 add_PP (mult_PP a (vec M A)) (mult_PP b (vec M B)) =
 mult_PP (a + b) (vec M C).
unfold vec in |- *; intros.
repeat rewrite <- distrib_mult_cons; auto.
replace (a * 1) with a; try ring; auto.
RingPP1 H0.
RingPP.
Qed.
 
Lemma calcul :
 forall P Q T U : PP,
 add_PP (add_PP P Q) (add_PP T U) = add_PP (add_PP P T) (add_PP Q U).
intros P Q T U; RingPP.
Qed.
 
Lemma add_PP_vecteur_rec :
 forall (a b : R) (A B C M : PO),
 a + b <> 0 ->
 add_PP (mult_PP a (vec M A)) (mult_PP b (vec M B)) =
 mult_PP (a + b) (vec M C) -> add_PP (cons a A) (cons b B) = cons (a + b) C.
unfold vec in |- *; intros.
repeat rewrite <- distrib_mult_cons in H0; auto.
replace a with (a * 1); try ring; auto.
rewrite calcul in H0.
replace b with (b * 1).
RingPP2 H0.
RingPP.
ring.
Qed.
 
Lemma add_PP_vecteur_opp :
 forall (a : R) (A B C M : PO),
 add_PP (mult_PP a (vec M A)) (mult_PP (- a) (vec M B)) = mult_PP a (vec B A).
intros; Ringvec.
Qed.
 
Lemma add_PP_assoc_permute :
 forall P Q T : PP, add_PP P (add_PP Q T) = add_PP (add_PP P T) Q :>PP.
intros P Q T; RingPP.
Qed.
 
Lemma vecteur_nul : forall (a : R) (A : PO), zero = mult_PP a (vec A A).
intros; Ringvec.
Qed.
 
Lemma mult_1_vec : forall A B : PO, mult_PP 1 (vec A B) = vec A B.
intros; Ringvec.
Qed.
 
Lemma add_PP_vec_reg :
 forall (P Q : PP) (a : R) (A B : PO),
 add_PP (mult_PP a (vec A B)) P = add_PP (mult_PP a (vec A B)) Q -> P = Q.
unfold vec in |- *; intros.
RingPP2 H.
RingPP.
Qed.
 
Lemma add_opp_vec :
 forall (k : R) (A B : PO),
 add_PP (mult_PP k (vec A B)) (mult_PP (- k) (vec A B)) = zero.
intros; Ringvec.
Qed.
 
Lemma mult_mult_vec :
 forall (A B : PO) (k k' : R),
 mult_PP k (mult_PP k' (vec A B)) = mult_PP (k * k') (vec A B) :>PP.
intros; Ringvec.
Qed.
 
Lemma distrib_mult_vec :
 forall (A B C D : PO) (k : R),
 mult_PP k (add_PP (vec A B) (vec C D)) =
 add_PP (mult_PP k (vec A B)) (mult_PP k (vec C D)) :>PP.
intros; Ringvec.
Qed.
 
Lemma conversion_PP :
 forall (a b : R) (A B : PO),
 cons a A = cons b B :>PP -> a <> 0 :>R -> a = b :>R -> A = B :>PO.
intros a b A B H H0 H1; try assumption.
elim cons_inj with (a := a) (b := b) (A := A) (B := B); intros;
 try assumption.
Qed.
 
Lemma produit_vecteur_nul :
 forall (a : R) (A B : PO), mult_PP a (vec A B) = zero -> a = 0 \/ A = B.
unfold vec in |- *; intros.
elim (classic (a = 0)); intros.
left; try assumption.
right; try assumption.
apply conversion_PP with (a := a) (b := a); try ring; auto.
cut (add_PP (cons (- a) A) (cons a B) = zero); intros.
RingPP2 H1.
RingPP.
rewrite <- H.
RingPP.
Qed.
 
Lemma vecteur_egalite_point :
 forall (a : R) (A B : PO), mult_PP a (vec A B) = zero -> a <> 0 -> A = B.
intros a A B H H0; try assumption.
generalize produit_vecteur_nul; intros.
elim H1 with (a := a) (A := A) (B := B);
 [ intros H2; try clear H1
 | intros H2; try clear H1; try exact H2
 | try clear H1 ].
absurd (a = 0); auto.
auto.
Qed.
 
Lemma distinct_produit_vecteur :
 forall (A B C : PO) (a : R),
 A <> B -> a <> 0 -> vec A C = mult_PP a (vec A B) :>PP -> A <> C.
intros; red in |- *; intros.
cut (~ (a = 0 \/ A = B)); intros.
apply H3.
apply produit_vecteur_nul.
rewrite <- H1.
rewrite H2; Ringvec.
intuition.
Qed.
 
Lemma vecteur_nul_conf : forall A B : PO, vec A B = zero -> A = B.
unfold vec in |- *; intros.
apply conversion_PP with (a := 1) (b := 1); auto.
RingPP2 H; RingPP.
discrR.
Qed.
 
Lemma distinct_egalite_vecteur :
 forall A B C D : PO, A <> B :>PO -> vec C D = vec A B :>PP -> C <> D :>PO.
red in |- *; intros.
apply H; apply vecteur_nul_conf.
rewrite <- H0; rewrite <- H1; Ringvec.
Qed.
 
Lemma inversion_colineaire :
 forall (k : R) (A B C : PO),
 A <> C -> vec A C = mult_PP k (vec A B) -> vec A B = mult_PP (/ k) (vec A C).
intros.
cut (k <> 0); intros.
rewrite H0.
Fieldvec k.
contrapose H.
apply vecteur_nul_conf.
rewrite H0; rewrite H1; Ringvec.
Qed.
Hint Resolve inversion_colineaire: geo.
 
Ltac subst_ A B :=
  match goal with
  | h:(A = B) |- _ => rewrite h || (try rewrite <- h); auto with geo
  end.
 
Ltac discrimine A B := elim (classic (A = B)); intro; [ subst_ A B | idtac ].
 
Lemma produit_zero_conf :
 forall (k : R) (A B C D : PO),
 vec A B = mult_PP k (vec C D) -> k = 0 -> A = B.
intros.
apply vecteur_nul_conf.
rewrite H; rewrite H0; Ringvec.
Qed.
 
Lemma egalite_vecteur_point :
 forall A B C : PO, vec C A = vec C B :>PP -> A = B :>PO.
intros.
apply vecteur_nul_conf.
replace (vec A B) with (add_PP (vec C B) (mult_PP (-1) (vec C A)));
 [ idtac | Ringvec ].
rewrite H; Ringvec.
Qed.
 
Ltac RReplace a b := replace a with b; [ idtac | try ring; auto with real ].
 
Ltac VReplace a b := replace a with b; [ idtac | Ringvec ].
 
Ltac FVReplace a b k := replace a with b; [ idtac | Fieldvec k ].
 
Lemma distinct_col_nonzero :
 forall (A B C D : PO) (x : R),
 A <> B -> vec A B = mult_PP x (vec C D) -> x <> 0.
intros.
contrapose H.
apply vecteur_nul_conf.
rewrite H0; rewrite H1.
Ringvec.
Qed.
 
Lemma distinct_col_nonun :
 forall (A B C : PO) (x : R),
 B <> C -> vec A C = mult_PP x (vec A B) -> 1 + - x <> 0.
intros.
contrapose H.
cut (x = 1); intros.
apply vecteur_nul_conf.
VReplace (vec B C) (add_PP (vec B A) (vec A C)).
rewrite H0.
subst_ x 1; Ringvec.
RReplace x (x + 0).
rewrite <- H1; ring.
Qed.
