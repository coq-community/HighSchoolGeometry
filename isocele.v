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


Require Export mediatrice.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition isocele (A B C : PO) : Prop := distance A B = distance A C.
 
Lemma isocele_permute : forall A B C : PO, isocele A B C -> isocele A C B.
unfold isocele in |- *; intros; auto.
Qed.
Hint Immediate isocele_permute: geo.
 
Lemma isocele_mediatrice :
 forall A B C : PO, isocele A B C -> mediatrice B C A.
unfold isocele, mediatrice in |- *; intros; auto.
Qed.
 
Lemma mediatrice_isocele :
 forall A B C : PO, mediatrice B C A -> isocele A B C.
unfold isocele, mediatrice in |- *; intros; auto.
Qed.
 
Lemma mediane_hauteur_isocele :
 forall A B C I : PO,
 I = milieu B C -> orthogonal (vec B C) (vec I A) -> isocele A B C.
intros.
apply mediatrice_isocele.
discrimine B C.
unfold mediatrice in |- *; auto with geo.
apply orthogonale_segment_milieu_mediatrice with I; auto.
Qed.
 
Lemma mediane_isocele_hauteur :
 forall A B C I : PO,
 I = milieu B C -> isocele A B C -> orthogonal (vec I A) (vec B C).
intros.
discrimine B C.
VReplace (vec C C) zero.
auto with geo.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
Qed.
 
Lemma hauteur_isocele_mediane :
 forall A B C I : PO,
 B <> C ->
 orthogonal (vec B C) (vec I A) ->
 isocele A B C -> alignes B C I -> I = milieu B C.
intros A B C I H0 H1 H2 H3; try assumption.
soit_projete B C A ipattern:H.
apply mediatrice_projete_milieu with A; auto.
rewrite <- H4.
apply unicite_projete_orthogonal with (3 := H1); auto.
Qed.
 
Lemma isocele_mediane_bissectrice :
 forall A B C I : PO,
 A <> I ->
 B <> C ->
 I = milieu B C ->
 isocele A B C -> cons_AV (vec A B) (vec A I) = cons_AV (vec A I) (vec A C).
intros.
apply mediatrice_milieu_angles; auto.
Qed.
 
Lemma isocele_angles_base :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 isocele A B C -> cons_AV (vec B C) (vec B A) = cons_AV (vec C A) (vec C B).
intros A B C H H0 H1; try assumption.
soit_milieu B C ipattern:K.
elim (classic (A = K)); intros.
apply permute_angles; auto.
rewrite <- H6 in H5.
rewrite <- H6 in H2.
rewrite <- (angles_milieu (A:=C) (B:=B) (C:=C) (I:=A)); auto.
rewrite <- (angles_milieu2 (A:=B) (B:=B) (C:=C) (I:=A)); auto with geo.
cut (orthogonal (vec B C) (vec K A)); intros.
cut (cons_AV (vec K B) (vec K A) = cons_AV (vec K A) (vec K C)); intros.
cut (cons_AV (vec A B) (vec A K) = cons_AV (vec A K) (vec A C)); intros.
rewrite (angles_milieu (A:=A) (B:=B) (C:=C) (I:=K)); auto.
generalize (somme_triangle (A:=A) (B:=B) (C:=K)); auto; intros.
generalize (somme_triangle (A:=A) (B:=K) (C:=C)); auto; intros.
rewrite (angles_milieu2 (A:=A) (B:=B) (C:=C) (I:=K)); auto.
replace (cons_AV (vec B K) (vec B A)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec A B) (vec A K)) (cons_AV (vec K A) (vec K B))))).
replace (cons_AV (vec C A) (vec C K)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec A K) (vec A C)) (cons_AV (vec K C) (vec K A))))).
rewrite H9.
replace (cons_AV (vec K C) (vec K A)) with (cons_AV (vec K A) (vec K B));
 auto with geo.
rewrite <- H11; auto.
mesure A K A C.
mesure K C K A.
mesure C A C K.
replace (x + (x0 + x1) + - (x + x0)) with x1; auto.
ring.
rewrite <- H10; auto.
mesure K A K B.
mesure A B A K.
mesure B K B A.
replace (x0 + (x1 + x) + - (x0 + x)) with x1; auto.
ring.
generalize (isocele_mediane_bissectrice (A:=A) (B:=B) (C:=C) (I:=K)); auto;
 intros.
generalize (milieu_angles_orthogonaux (A:=B) (B:=C) (M:=K) (N:=A)); auto;
 intros.
generalize (mediane_isocele_hauteur (A:=A) (B:=B) (C:=C) (I:=K));
 auto with geo; intros.
Qed.
 
Lemma diametre_rectangle :
 forall A B C C' : PO,
 A <> B ->
 C' = milieu A B ->
 distance C' C = distance C' A -> orthogonal (vec C A) (vec C B).
intros.
discrimine C A.
apply ortho_sym.
replace (vec A A) with zero.
apply zero_ortho_tout.
Ringvec.
discrimine C B.
replace (vec B B) with zero.
apply zero_ortho_tout.
Ringvec.
cut (B <> C'); intros.
cut (A <> C'); intros.
cut (C <> C'); intros.
apply angles_orthogonal; auto.
cut (isocele C' C A); intros.
cut (isocele C' B C); intros.
generalize (isocele_angles_base (A:=C') (B:=C) (C:=A)); auto; intros.
generalize (isocele_angles_base (A:=C') (B:=B) (C:=C)); auto; intros.
generalize (somme_triangle (A:=C') (B:=C) (C:=A)); intros.
generalize (somme_triangle (A:=C') (B:=B) (C:=C)); intros.
replace (double_AV (cons_AV (vec C A) (vec C B))) with
 (plus (double_AV (cons_AV (vec C A) (vec C C')))
    (double_AV (cons_AV (vec C C') (vec C B)))).
replace (double_AV (cons_AV (vec C A) (vec C C'))) with
 (plus (cons_AV (vec C A) (vec C C')) (cons_AV (vec A C') (vec A C))).
replace (double_AV (cons_AV (vec C C') (vec C B))) with
 (plus (cons_AV (vec B C) (vec B C')) (cons_AV (vec C C') (vec C B))).
replace (plus (cons_AV (vec B C) (vec B C')) (cons_AV (vec C C') (vec C B)))
 with (plus (image_angle pi) (opp (cons_AV (vec C' B) (vec C' C)))).
replace (plus (cons_AV (vec C A) (vec C C')) (cons_AV (vec A C') (vec A C)))
 with (plus (image_angle pi) (opp (cons_AV (vec C' C) (vec C' A)))).
rewrite def_opp; auto.
rewrite def_opp; auto.
mesure C' A C' C.
mesure C' C C' B.
replace (pi + x + (pi + x0)) with (pi + pi + (x + x0)).
replace (pi + pi) with deuxpi; auto.
rewrite add_mes_compatible; rewrite pi_plus_pi; rewrite <- add_mes_compatible.
replace (0 + (x + x0)) with (x + x0); auto.
rewrite add_mes_compatible.
rewrite H14; rewrite H13.
replace
 (plus (cons_AV (vec C' A) (vec C' C)) (cons_AV (vec C' C) (vec C' B))) with
 (cons_AV (vec C' A) (vec C' B)).
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=C')); auto.
rewrite <- angle_plat; auto.
rewrite Chasles; auto.
ring.
ring.
rewrite <- H11; auto.
rewrite <- H9; auto.
mesure C' C C' A.
mesure C A C C'.
replace (x + (x0 + x0) + - x) with (x0 + x0); auto.
ring.
rewrite <- H12; auto.
rewrite <- H10; auto.
mesure C' B C' C.
mesure B C B C'.
replace (x + (x0 + x0) + - x) with (x0 + x0); auto.
ring.
rewrite H10; auto.
rewrite H9; auto.
rewrite double_Chasles; auto.
unfold isocele in |- *.
rewrite H1.
apply carre_scalaire_egalite_distance.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=C')); auto.
replace (vec A C') with (mult_PP (-1) (vec C' A)); auto.
Simplscal.
Ringvec.
unfold isocele in |- *.
rewrite H1; auto.
apply isometrie_distinct with (1 := H5).
rewrite distance_sym.
rewrite <- H1; rewrite distance_sym; auto.
rewrite H0.
apply milieu_distinct; auto.
rewrite H0.
apply milieu_distinct2; auto.
Qed.