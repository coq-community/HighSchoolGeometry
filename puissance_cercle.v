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


Require Export contact.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma scalaire_diametre :
 forall A A' B O M : PO,
 A <> B ->
 O = milieu A A' ->
 cercle_diametre A A' B ->
 alignes A B M ->
 scalaire (vec M A) (vec M B) = Rsqr (distance M O) + - Rsqr (distance O A).
intros A A' B O M H0 H1 H2 H3; try assumption.
generalize H2; unfold cercle_diametre in |- *; intros.
elim H4;
 [ intros O' H5; elim H5; [ intros H6 H7; try clear H5 H4; try exact H7 ] ].
assert (O' = O).
rewrite H1; auto.
rewrite H in H6; clear H O' H7.
discrimine A A'.
assert (A = B).
apply cercle_diametre_degenere with A'; auto.
rewrite <- H4.
rewrite (scalaire_difference_carre (A:=A') (B:=A) (I:=O) M); auto with geo.
elim (classic (alignes A A' B)); intros.
assert (B = A').
elim alignes_diametre with (A := A) (B := B) (A' := A');
 [ intros H12; try clear alignes_diametre
 | intros H12; try clear alignes_diametre; try exact H12
 | auto
 | auto ].
absurd (A = B); auto.
rewrite H5.
rewrite (scalaire_difference_carre (A:=A) (B:=A') (I:=O) M); auto.
assert (triangle A A' B); auto with geo.
discrimine M A.
unfold Rsqr in |- *; repeat rewrite <- carre_scalaire_distance.
VReplace (vec A O) (mult_PP (-1) (vec O A)).
VReplace (vec A A) (mult_PP 0 (vec O A)).
Simplscal.
rewrite <- (scalaire_avec_projete (A:=M) (B:=A) (C:=A') (H:=B)); auto.
apply scalaire_difference_carre; auto.
apply alignes_ordre_cycle2; auto.
assert (orthogonal (vec B A) (vec B A')).
apply triangle_diametre with O; auto with geo.
apply circonscrit_permute; auto.
halignes H3 ipattern:k.
replace (vec M A) with (mult_PP k (vec B A)).
Simplortho.
VReplace (vec M A) (mult_PP (-1) (vec A M)).
rewrite H9; Ringvec.
Qed.
 
Theorem puissance_cercle :
 forall A B C D M : PO,
 triangle A B C ->
 C <> D ->
 sont_cocycliques A B C D ->
 alignes A B M ->
 alignes C D M -> scalaire (vec M A) (vec M B) = scalaire (vec M C) (vec M D).
intros A B C D M H H20 H0 H2 H3; try assumption.
elim cocycliques_existence_diametre with (A := A) (B := B) (C := C) (D := D);
 [ intros A' H1; try clear cocycliques_existence_diametre; try exact H1
 | auto ].
generalize H0; generalize H1;
 unfold sont_cocycliques, diametre_circonscrit in |- *; 
 intros.
elim H4;
 [ intros O1 H6; elim H6; [ intros H7 H8; try clear H6 H4; try exact H8 ] ].
elim H5;
 [ intros O H4; elim H4; [ intros H6 H9; try clear H4 H5; try exact H9 ] ].
assert (O1 = O).
apply (unicite_circonscrit_triangle H H8 H6); auto.
rewrite H4 in H7; clear H8 H4.
deroule_triangle A B C.
deroule_circonscrit A B C O.
rewrite (scalaire_diametre (A:=A) (A':=A') (B:=B) (O:=O) (M:=M)); auto.
hcercle H9; hcercle H6.
replace (Rsqr (distance O A)) with (Rsqr (distance O C)).
symetrique O C ipattern:C'.
rewrite (scalaire_diametre (A:=C) (A':=C') (B:=D) (O:=O) (M:=M)); auto.
apply changement_diametre with (2 := H6); auto.
rewrite <- H18; auto.
apply circonscrit_diametre with (1 := H6); auto.
Qed.
 
Theorem puissance_cercle_tangente :
 forall A B C O M : PO,
 triangle A B C ->
 circonscrit O A B C ->
 alignes A B M ->
 tangente_cercle O A C M ->
 Rsqr (distance M C) = scalaire (vec M A) (vec M B).
unfold tangente_cercle in |- *; intros; applatit_and.
symetrique O A ipattern:A'.
deroule_triangle A B C.
deroule_circonscrit A B C O.
hcercle H0.
clear H3.
rewrite (scalaire_diametre (A:=A) (A':=A') (B:=B) (O:=O) (M:=M)); auto.
elim (Pythagore C O M); intros.
replace (Rsqr (distance O A)) with (Rsqr (distance O C)).
rewrite (distance_sym M O).
rewrite H3; auto with geo.
rewrite (distance_sym M C); rewrite (distance_sym O C); ring.
rewrite <- H15; auto.
apply circonscrit_diametre with (1 := H0); auto.
Qed.
 
Theorem egalite_puissance_cocycliques :
 forall A B C D M : PO,
 triangle A B C ->
 M <> C ->
 alignes A B M ->
 alignes C D M ->
 scalaire (vec M A) (vec M B) = scalaire (vec M C) (vec M D) ->
 sont_cocycliques A B C D.
unfold sont_cocycliques in |- *; intros A B C D M H10 H0 H1 H2 H3.
elim existence_cercle_circonscrit with (A := A) (B := B) (C := C);
 [ intros O H4; try clear existence_cercle_circonscrit; try exact H4 | auto ].
exists O; split; auto.
elim existence_projete_orthogonal with (A := M) (B := C) (C := O);
 [ intros H H6; try clear existence_projete_orthogonal; try exact H6 | auto ].
elim def_projete_orthogonal2 with (A := M) (B := C) (C := O) (H := H);
 [ intros; auto | auto | auto ].
assert (alignes M C D); auto with geo.
halignes H8 ipattern:k'.
halignes H5 ipattern:k.
discrimine H C.
assert (Rsqr (distance M C) = scalaire (vec M A) (vec M B)).
apply puissance_cercle_tangente with O; auto.
hcercle H4.
rewrite <- H12.
replace (vec H M) with (mult_PP (- k) (vec M C)).
auto with geo.
VReplace (vec H M) (mult_PP (-1) (vec M H)).
rewrite H11; Ringvec.
assert (k' = 1).
apply Rmult_eq_reg_l with (scalaire (vec M C) (vec M C)); auto with geo.
replace (scalaire (vec M C) (vec M C) * k') with
 (scalaire (vec M C) (vec M D)).
rewrite carre_scalaire_distance.
unfold Rsqr in H13.
rewrite H13; rewrite H3; ring.
rewrite H9; Simplscal.
assert (D = C).
apply egalite_vecteur_point with M.
rewrite H9; rewrite H14; Ringvec.
rewrite H15; auto.
elim intersection2_cercle_droite with (A := C) (B := M) (O := O) (H := H);
 [ intros E H13; elim H13;
    [ intros H14 H15; elim H15;
       [ unfold cercle_rayon, isocele in |- *; intros H16 H17;
          try clear H15 H13; try exact H17 ] ]
 | auto
 | auto
 | auto
 | auto ].
assert (sont_cocycliques A B C E).
exists O; split; auto.
generalize H4; unfold circonscrit, isocele in |- *; intros; applatit_and.
split; [ try assumption | idtac ].
rewrite <- H17; auto.
assert (scalaire (vec M C) (vec M D) = scalaire (vec M C) (vec M E)).
rewrite <- H3.
apply puissance_cercle; auto.
auto with geo.
assert (alignes M C E); auto with geo.
halignes H18 ipattern:k1.
assert (k' = k1).
apply Rmult_eq_reg_l with (scalaire (vec M C) (vec M C)); auto with geo.
replace (scalaire (vec M C) (vec M C) * k') with
 (scalaire (vec M C) (vec M D)).
rewrite H15; rewrite H19; Simplscal.
rewrite H9; Simplscal.
assert (D = E).
apply egalite_vecteur_point with M.
rewrite H9; rewrite H20; rewrite H19; auto.
rewrite H21.
generalize H13; unfold sont_cocycliques in |- *; intros.
elim H22;
 [ intros O1 H23; elim H23;
    [ intros H24 H25; try clear H23 H22; try exact H25 ] ].
assert (O1 = O).
apply (unicite_circonscrit_triangle H10 H24 H4); auto.
rewrite H22 in H25; auto.
deroule_circonscrit A B C O.
try exact H15.
apply def_projete_orthogonal; auto with geo.
apply projete_distance_Rlt with M; auto.
Qed.
 
Lemma puissance_cercle_tangente_rec :
 forall A B C O M : PO,
 triangle A B C ->
 circonscrit O A B C ->
 alignes A B M ->
 Rsqr (distance M C) = scalaire (vec M A) (vec M B) ->
 tangente_cercle O A C M.
intros.
deroule_circonscrit A B C O.
deroule_triangle A B C.
hcercle H0.
symetrique O A ipattern:A'.
rewrite (scalaire_diametre (A:=A) (A':=A') (B:=B) (O:=O) (M:=M)) in H2; auto.
elim (Pythagore C M O); intros.
apply H15.
rewrite (distance_sym C M).
rewrite H2; rewrite H12.
rewrite (distance_sym O C); ring.
apply circonscrit_diametre with (1 := H0); auto.
Qed.
 
Definition puissance_point_cercle (M O A : PO) :=
  Rsqr (distance O M) + - Rsqr (distance O A).