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


Require Export cocyclicite.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma triangle_rectangle_demi_cercle :
 forall A B C : PO,
 triangle A B C ->
 orthogonal (vec A B) (vec A C) ->
 ex
   (fun O : PO =>
    circonscrit O A B C /\ cons_AV (vec O B) (vec O C) = image_angle pi).
intros; deroule_triangle A ipattern:B ipattern:C.
soit_circonscrit A B C ipattern:D.
exists D.
split; [ try assumption | idtac ].
rewrite <- (angle_inscrit (O:=D) (A:=A) (B:=B) (C:=C)); auto.
apply orthogonal_angles; auto.
Qed.
 
Lemma triangle_demi_cercle_rectangle :
 forall A B C O : PO,
 triangle A B C ->
 circonscrit O A B C ->
 cons_AV (vec O B) (vec O C) = image_angle pi ->
 orthogonal (vec A B) (vec A C).
intros; deroule_triangle A ipattern:B ipattern:C.
deroule_circonscrit A B C O.
apply angles_orthogonal; auto.
rewrite (angle_inscrit (O:=O) (A:=A) (B:=B) (C:=C)); auto.
Qed.
 
Lemma triangle_diametre :
 forall A B C O : PO,
 triangle A B C ->
 O = milieu B C -> circonscrit O A B C -> orthogonal (vec A B) (vec A C).
intros.
apply triangle_demi_cercle_rectangle with O; auto.
deroule_circonscrit A B C O.
replace (cons_AV (vec O B) (vec O C)) with
 (plus (cons_AV (vec O B) (vec O A)) (cons_AV (vec O A) (vec O C))).
deroule_triangle A B C.
rewrite (milieu_angles (A:=B) (B:=C) (M:=O) (N:=A)); auto.
rewrite <- (def_opp (A:=O) (B:=A) (C:=O) (D:=C)); auto.
mesure O A O C.
RReplace (- x + pi + x) pi; auto.
rewrite Chasles; auto.
Qed.
 
Lemma triangle_rectangle_cercle_diametre :
 forall A B C : PO,
 A <> B -> A <> C -> orthogonal (vec A B) (vec A C) -> cercle_diametre B C A.
icercle.
assert (triangle A B C).
unfold triangle in |- *.
apply orthogonal_non_alignes; auto.
elim triangle_rectangle_demi_cercle with (A := A) (B := B) (C := C);
 [ intros O' H3; elim H3; [ intros H4 H5; try clear H3; try exact H5 ]
 | auto
 | auto ].
exists O'.
hcercle H4.
split; [ idtac | auto ].
rewrite <- H6; auto.
assert (vec O' C = mult_PP (-1) (vec O' B)).
deroule_circonscrit A B C O'.
apply (alignes_distance_negatif_colineaire (k:=1) (A:=O') (B:=B) (C:=C));
 auto.
rewrite <- H6; rewrite <- H7; ring.
apply egalite_vecteur_milieu.
rewrite H3; Ringvec.
Qed.
 
Lemma ligne_niveau_MAMB_O :
 forall A B M : PO, scalaire (vec M A) (vec M B) = 0 -> cercle_diametre A B M.
intros.
discrimine M A.
discrimine M B.
apply triangle_rectangle_cercle_diametre; auto with geo.
Qed.
 
Theorem caracterisation_cercle_diametre :
 forall A B M : PO,
 cercle_diametre A B M <-> scalaire (vec M A) (vec M B) = 0.
red in |- *; try split; intros.
hcercle H.
elim H0;
 [ intros O H1; elim H1; [ intros H2 H3; try clear H1 H0; try exact H3 ] ].
discrimine A B.
assert (A = M).
apply cercle_diametre_degenere with B; auto.
rewrite <- H1; rewrite H0.
VReplace (vec B B) (mult_PP 0 (vec B B)).
Simplscal.
elim (classic (alignes A B M)); intros.
elim alignes_diametre with (A := A) (B := M) (A' := B); intros; auto.
rewrite H4.
VReplace (vec A A) (mult_PP 0 (vec B B)).
Simplscal.
rewrite H4.
VReplace (vec B B) (mult_PP 0 (vec B B)).
Simplscal.
assert (triangle A B M); (unfold triangle in |- *; auto).
assert (orthogonal (vec M A) (vec M B)).
apply (triangle_diametre (A:=M) (B:=A) (C:=B) (O:=O)); auto with geo.
icercle.
rewrite <- H6; auto.
apply def_orthogonal; auto with geo.
apply ligne_niveau_MAMB_O; auto.
Qed.
 
Lemma ligne_niveau_MAMB_k :
 forall (A B I M : PO) (k : R),
 k + Rsqr (distance I A) >= 0 ->
 I = milieu A B ->
 scalaire (vec M A) (vec M B) = k ->
 cercle I (sqrt (k + Rsqr (distance I A))) M.
intros A B I M k H H0; try assumption.
rewrite (scalaire_difference_carre (A:=A) (B:=B) (I:=I) M); auto.
icercle.
assert (Rsqr (distance I M) = k + Rsqr (distance I A)).
rewrite <- distance_sym; rewrite <- H1; ring.
apply Rsqr_inj; auto with geo real.
rewrite Rsqr_sqrt; auto with real.
Qed.
 
Lemma homothetie_cercle_diametre :
 forall (k : R) (I A A' B B' M M' : PO),
 k <> 0 :>R ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B :>PO ->
 M' = homothetie k I M :>PO ->
 cercle_diametre A B M -> cercle_diametre A' B' M'.
icercle.
elim H3;
 [ intros O H4; elim H4;
    [ intros H5 H6; elim H5;
       [ intros H7 H8; try clear H5 H4 H3; try exact H8 ] ] ].
elim existence_homothetique with (k := k) (I := I) (A := O);
 [ intros O' H3; try clear existence_homothetique; try exact H3 ].
exists O'; (split; auto).
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=O) (B:=A) (A':=O') (B':=A'));
 intros.
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=O) (B:=M) (A':=O') (B':=M'));
 intros.
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=O) (B:=B) (A':=O') (B':=B'));
 intros.
split; apply carre_scalaire_egalite_distance.
rewrite H4; auto.
rewrite H9; auto.
Simplscal.
repeat rewrite carre_scalaire_distance; auto.
rewrite H7; ring.
rewrite H4; auto.
rewrite H5; auto.
Simplscal.
repeat rewrite carre_scalaire_distance; auto.
rewrite H8; ring.
rewrite H3.
rewrite
 (homothetie_milieu (k:=k) (I:=I) (A:=A) (A':=A') (B:=B) (B':=B') (M:=O)
    (N:=milieu A' B')); auto.
Qed.
 
Definition diametre_circonscrit (A A' B C : PO) :=
  exists O : PO, O = milieu A A' /\ circonscrit O A B C.
 
Lemma cocyclicite_cercle_diametre :
 forall A B C D A' : PO,
 triangle A B C ->
 sont_cocycliques A B C D ->
 diametre_circonscrit A A' B C -> diametre_circonscrit A A' C D.
unfold sont_cocycliques, diametre_circonscrit in |- *; intros.
elim H0;
 [ intros O1 H3; elim H3; [ intros H4 H5; try clear H3 H0; try exact H5 ] ].
elim H1;
 [ intros O H0; elim H0; [ intros H2 H3; try clear H0 H1; try exact H3 ] ].
assert (O1 = O).
apply (unicite_circonscrit_triangle H H4 H3); auto.
rewrite H0 in H5; clear H4 H0.
exists O.
split; [ try assumption | idtac ].
hcercle H3.
hcercle H5.
Qed.
 
Lemma diametre_circonscrit_centre :
 forall A B C A' O : PO,
 triangle A B C ->
 circonscrit O A B C ->
 diametre_circonscrit A A' B C -> cercle_diametre A A' B.
unfold sont_cocycliques, diametre_circonscrit in |- *; intros.
elim H1;
 [ intros O1 H2; elim H2; [ intros H3 H4; try clear H2 H1; try exact H4 ] ].
assert (O1 = O).
apply (unicite_circonscrit_triangle H H4 H0); auto.
rewrite H1 in H3; clear H4 H1.
apply circonscrit_diametre with (C := C) (O := O); auto.
Qed.
 
Lemma changement_diametre :
 forall A B C D C' O : PO,
 triangle A B C ->
 circonscrit O A B C ->
 O = milieu C C' -> sont_cocycliques A B C D -> cercle_diametre C C' D.
unfold cercle_diametre, sont_cocycliques in |- *; intros.
elim H2;
 [ intros O1 H3; elim H3; [ intros H4 H5; try clear H3 H2; try exact H5 ] ].
assert (O1 = O).
apply (unicite_circonscrit_triangle H H4 H0); auto.
rewrite H2 in H5; clear H4 H2.
hcercle H5; hcercle H0.
exists O.
icercle.
icercle.
rewrite <- H7; auto.
Qed.
 
Lemma cocycliques_existence_diametre :
 forall A B C D : PO,
 sont_cocycliques A B C D -> exists A' : PO, diametre_circonscrit A A' B C.
intros.
generalize H; unfold sont_cocycliques, diametre_circonscrit in |- *; intros.
elim H0;
 [ intros O H1; elim H1; [ intros H2 H3; try clear H1 H0; try exact H3 ] ].
symetrique O A ipattern:A'.
exists A'; exists O.
tauto.
Qed.