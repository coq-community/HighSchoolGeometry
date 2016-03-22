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


Require Export representant_unitaire.
Set Implicit Arguments.
Unset Strict Implicit.
Hint Resolve distance_non_nulle scalaire_positif: geo.
 
Definition distance (A B : PO) := sqrt (scalaire (vec A B) (vec A B)).
 
Lemma distance_pos : forall A B : PO, distance A B >= 0.
unfold distance in |- *; intros; auto with geo real.
Qed.
 
Lemma distance_sym : forall A B : PO, distance A B = distance B A.
unfold distance in |- *; intros; auto.
VReplace (vec B A) (mult_PP (-1) (vec A B)).
Simplscal.
replace (-1 * -1 * scalaire (vec A B) (vec A B)) with
 (scalaire (vec A B) (vec A B)); try ring.
Qed.
 
Lemma distance_refl : forall A B : PO, distance A B = 0 <-> A = B.
unfold distance in |- *; intros; red in |- *.
split; [ idtac | try assumption ].
intros H; try assumption.
apply distance_nulle.
RReplace 0 (0 * 0).
rewrite <- H; auto.
symmetry  in |- *.
apply def_sqrt; auto with geo real.
intros.
rewrite <- H; auto.
VReplace (vec A A) (mult_PP (-0) (vec A B)).
Simplscal.
replace (-0 * -0 * scalaire (vec A B) (vec A B)) with 0; try ring.
try exact sqrt_0.
Qed.
 
Lemma distance_refl1 : forall A B : PO, distance A B = 0 :>R -> A = B :>PO.
intros.
elim (distance_refl A B); auto.
Qed.
 
Lemma distance_refl2 : forall A B : PO, A = B :>PO -> distance A B = 0 :>R.
intros.
elim (distance_refl A B); auto.
Qed.
Hint Resolve distance_refl1 distance_refl2: geo.
 
Lemma caract_representant_unitaire :
 forall A B C : PO,
 A <> B ->
 vec A C = representant_unitaire (vec A B) ->
 vec A C = mult_PP (/ distance A B) (vec A B).
unfold distance in |- *; intros.
cut
 (alignes A B C /\
  scalaire (vec A C) (vec A C) = 1 /\ scalaire (vec A B) (vec A C) >= 0);
 intros.
elim H1; intros H2 H3; elim H3; intros H4 H5; try clear H3 H1; try exact H5.
halignes H2 ipattern:k.
rewrite H1 in H4.
cut (/ scalaire (vec A B) (vec A B) = k * k); intros.
cut (k = sqrt (/ scalaire (vec A B) (vec A B))); intros.
rewrite H1; rewrite H6.
rewrite sqrt_Rinv; auto with geo real.
apply inversion_sqr; auto with geo real.
rewrite H1 in H5.
replace k with
 (k * scalaire (vec A B) (vec A B) * / scalaire (vec A B) (vec A B)).
replace (k * scalaire (vec A B) (vec A B)) with
 (scalaire (vec A B) (mult_PP k (vec A B))).
apply Rmult_pos; auto with geo real.
Simplscal.
field; auto with geo.
replace (/ scalaire (vec A B) (vec A B)) with
 (1 * / scalaire (vec A B) (vec A B)).
rewrite <- H4.
Simplscal.
field; auto with geo.
field; auto with geo.
apply def_representant_unitaire2; auto.
Qed.
 
Lemma distance_vecteur :
 forall A B : PO,
 A <> B -> vec A B = mult_PP (distance A B) (representant_unitaire (vec A B)).
unfold distance in |- *; intros.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros C H0; try clear existence_unitaire; try exact H0 | auto ].
rewrite <- H0; auto.
rewrite (caract_representant_unitaire (A:=A) (B:=B) (C:=C)); auto.
unfold distance in |- *.
cut (sqrt (scalaire (vec A B) (vec A B)) <> 0); intros.
Fieldvec (sqrt (scalaire (vec A B) (vec A B))).
auto with *.
Qed.
 
Lemma dist_non_nulle : forall A B : PO, distance A B <> 0 -> A <> B.
unfold distance in |- *; red in |- *; intros.
apply H.
rewrite H0.
replace (scalaire (vec B B) (vec B B)) with 0.
rewrite sqrt_0; ring.
replace (vec B B) with (mult_PP 0 (vec A B)).
Simplscal.
Ringvec.
Qed.
Hint Resolve distance_pos dist_non_nulle: geo.
 
Lemma distincts_dist_non_nulle : forall A B : PO, A <> B -> distance A B <> 0.
unfold distance in |- *; intros; red in |- *; intros.
apply H.
apply distance_nulle.
rewrite <- (def_sqrt (scalaire (vec A B) (vec A B))); auto with geo.
rewrite H0; ring.
Qed.
Hint Resolve distincts_dist_non_nulle: geo.
 
Lemma isometrie_distinct :
 forall A B A' B' : PO, A <> B -> distance A B = distance A' B' -> A' <> B'.
intros.
apply dist_non_nulle; rewrite <- H0; auto with geo.
Qed.
 
Lemma carre_scalaire_distance :
 forall A B : PO, scalaire (vec A B) (vec A B) = distance A B * distance A B.
unfold distance in |- *; intros.
rewrite def_sqrt; auto with geo.
Qed.
 
Lemma carre_egalite_distance :
 forall A B C D : PO,
 distance A B * distance A B = distance C D * distance C D ->
 distance A B = distance C D.
intros.
apply resolution; auto with geo.
Qed.
 
Lemma distance_carre :
 forall A B C D : PO,
 Rsqr (distance A B) = Rsqr (distance C D) -> distance A B = distance C D.
unfold Rsqr in |- *; intros.
apply carre_egalite_distance; auto with geo.
Qed.
Hint Resolve carre_egalite_distance distance_carre: geo.
 
Lemma carre_scalaire_egalite_distance :
 forall A B C D : PO,
 scalaire (vec A B) (vec A B) = scalaire (vec C D) (vec C D) ->
 distance A B = distance C D.
intros.
apply carre_egalite_distance.
repeat rewrite <- carre_scalaire_distance; auto with geo.
Qed.
 
Lemma unitaire_distincts2 : forall A B : PO, distance A B = 1 -> A <> B.
intros.
apply dist_non_nulle.
rewrite H.
discrR.
Qed.
Hint Resolve unitaire_distincts2: geo.
 
Lemma distance_1_representant :
 forall A B : PO,
 distance A B = 1 -> vec A B = representant_unitaire (vec A B).
intros.
apply def_representant_unitaire; auto with geo.
rewrite carre_scalaire_distance; rewrite H; ring.
Qed.
 
Lemma distance_1_carre_scalaire :
 forall A B : PO, distance A B = 1 -> scalaire (vec A B) (vec A B) = 1.
intros.
rewrite carre_scalaire_distance.
rewrite H; ring.
Qed.
 
Lemma carre_scalaire_1_distance :
 forall A B : PO, scalaire (vec A B) (vec A B) = 1 -> distance A B = 1.
intros.
unfold distance in |- *.
rewrite H.
rewrite sqrt_1; auto with geo.
Qed.
Hint Resolve carre_scalaire_1_distance distance_1_carre_scalaire
  distance_1_representant: geo.
 
Lemma milieu_distance :
 forall A B I : PO, I = milieu A B -> distance I A = distance I B.
intros.
apply carre_scalaire_egalite_distance.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=I)); auto with geo.
replace (vec I A) with (mult_PP (-1) (vec A I)); [ idtac | Ringvec ].
Simplscal.
Qed.
Hint Resolve milieu_distance: geo.
 
Lemma egalite_vecteur_distance :
 forall A B C D : PO, vec A B = vec C D -> distance A B = distance C D :>R.
intros.
apply carre_scalaire_egalite_distance.
rewrite H; auto.
Qed.
 
Lemma colinearite_distance :
 forall (k : R) (A B C D : PO),
 vec C D = mult_PP k (vec A B) :>PP -> distance C D = Rabs k * distance A B.
unfold distance in |- *; intros.
rewrite H; Simplscal.
replace (k * k) with (Rsqr k); auto with real.
rewrite sqrt_mult; auto with real geo.
rewrite sqrt_Rsqr_abs; ring.
Qed.
Hint Resolve colinearite_distance: geo.