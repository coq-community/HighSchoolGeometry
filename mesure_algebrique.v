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


Require Export barycentre.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter mes_alg : PO -> PO -> R.
 
Axiom
  def_mes_alg :
    forall (A B C D : PO) (k : R),
    vec C D = mult_PP k (vec A B) :>PP -> mes_alg C D = k * mes_alg A B :>R.
 
Axiom
  def_mes_alg2 :
    forall (A B C D : PO) (k : R),
    mes_alg C D = k * mes_alg A B :>R ->
    col_vec A B C D -> vec C D = mult_PP k (vec A B) :>PP.
 
Lemma mes_alg_BA : forall A B : PO, mes_alg B A = - mes_alg A B :>R.
intros.
RReplace (- mes_alg A B) (-1 * mes_alg A B).
apply def_mes_alg.
Ringvec.
Qed.
 
Lemma mes_alg_nulle : forall A B : PO, mes_alg A B = 0 :>R -> A = B.
intros.
apply vecteur_nul_conf.
replace zero with (mult_PP 0 (vec A B)).
apply def_mes_alg2.
rewrite H; ring.
unfold col_vec in |- *.
exists 1.
Ringvec.
Ringvec.
Qed.
 
Lemma mes_alg_conf : forall A B : PO, A = B -> mes_alg A B = 0 :>R.
intros.
rewrite H.
replace 0 with (0 * mes_alg A A).
apply def_mes_alg.
Ringvec.
ring.
Qed.
Hint Resolve mes_alg_conf mes_alg_nulle: geo.
 
Lemma Chasles_mes_alg :
 forall A B C : PO, alignes A B C -> mes_alg A B + mes_alg B C = mes_alg A C.
intros.
halignes H ipattern:k.
rewrite (mes_alg_conf (A:=B) (B:=B)); auto; ring.
replace (mes_alg A B) with (1 * mes_alg A B).
replace (mes_alg B C) with ((k + -1) * mes_alg A B).
replace (mes_alg A C) with (k * mes_alg A B).
ring.
symmetry  in |- *; apply def_mes_alg; auto.
symmetry  in |- *; apply def_mes_alg; auto.
VReplace (vec B C) (add_PP (vec A C) (mult_PP (-1) (vec A B))).
rewrite H0; Ringvec.
symmetry  in |- *; apply def_mes_alg; Ringvec.
Qed.
 
Lemma existence_mes_algebrique :
 forall (k : R) (A B : PO),
 exists C : PO, alignes A B C /\ mes_alg A C = k * mes_alg A B.
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 [ intros C H; try clear existence_representant_mult_vecteur; try exact H ].
exists C.
cut (mes_alg A C = k * mes_alg A B); intros.
split; [ idtac | try assumption ].
apply colineaire_alignes with k; auto.
apply def_mes_alg; auto.
Qed.
 
Lemma vecteur_quotient_mes_algebrique :
 forall (A B C D : PO) (k : R),
 A <> B -> vec C D = mult_PP k (vec A B) -> mes_alg C D / mes_alg A B = k.
intros.
rewrite (def_mes_alg H0); auto.
field.
contrapose H.
apply mes_alg_nulle; auto.
Qed.
 
Lemma quotient_mes_algebrique_vecteur :
 forall (A B C D : PO) (k : R),
 A <> B ->
 col_vec A B C D ->
 mes_alg C D / mes_alg A B = k -> vec C D = mult_PP k (vec A B).
intros.
apply def_mes_alg2; auto.
assert (mes_alg A B <> 0).
contrapose H.
apply mes_alg_nulle; auto.
RReplace (mes_alg C D) (mes_alg C D / mes_alg A B * mes_alg A B).
rewrite H1; auto.
field; auto.
Qed.
Hint Resolve def_mes_alg2 def_mes_alg: geo.
 
Lemma colineaire_mes_alg_conf :
 forall (A B C D : PO) (k : R),
 A <> B ->
 col_vec A B A C ->
 col_vec A B A D ->
 mes_alg A C = k * mes_alg A B -> mes_alg A D = k * mes_alg A B -> C = D.
intros.
assert (vec A C = mult_PP k (vec A B)); auto with geo.
assert (vec A D = mult_PP k (vec A B)); auto with geo.
apply vecteur_nul_conf.
VReplace (vec C D) (add_PP (vec A D) (mult_PP (-1) (vec A C))).
rewrite H5; rewrite H4; Ringvec.
Qed.
 
Lemma barycentre_mes_alg :
 forall (a b : R) (A B G : PO),
 a + b <> 0 :>R ->
 G = barycentre (cons a A) (cons b B) :>PO ->
 a * mes_alg G A + b * mes_alg G B = 0 :>R.
intros.
cut (a <> 0 \/ b <> 0); intros.
elim H1; [ intros H2; try clear H1 | intros H2; try clear H1; try exact H2 ].
cut (mes_alg G A = / a * - b * mes_alg G B); intros.
rewrite H1.
RReplace (a * (/ a * - b * mes_alg G B)) (a * / a * (- b * mes_alg G B)).
RReplace (a * / a) 1.
ring.
apply def_mes_alg.
apply mult_PP_regulier with a; auto.
replace (mult_PP a (mult_PP (/ a * - b) (vec G B))) with
 (add_PP (mult_PP (- b) (vec G B)) zero).
rewrite <- (def_vecteur_bary (a:=a) (b:=b) (A:=A) (B:=B) (G:=G)); auto.
Ringvec.
Fieldvec a.
cut (mes_alg G B = / b * - a * mes_alg G A); intros.
rewrite H1.
RReplace (b * (/ b * - a * mes_alg G A)) (b * / b * (- a * mes_alg G A)).
RReplace (b * / b) 1.
ring.
apply def_mes_alg.
apply mult_PP_regulier with b; auto.
replace (mult_PP b (mult_PP (/ b * - a) (vec G A))) with
 (add_PP (mult_PP (- a) (vec G A)) zero).
rewrite <- (def_vecteur_bary (a:=a) (b:=b) (A:=A) (B:=B) (G:=G)); auto.
Ringvec.
Fieldvec b.
apply not_and_or.
red in |- *; intros; apply H.
elim H1; intros H2 H3; try clear H1; try exact H3.
rewrite H2; rewrite H3; ring.
Qed.