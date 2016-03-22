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


Require Export composee_translation_rotation.
Set Implicit Arguments.
Unset Strict Implicit.
 
Theorem composee_rotation_IJ_translation :
 forall (I J : PO) (a b : R),
 image_angle (a + b) = image_angle 0 ->
 exists A : PO,
   (exists B : PO,
      (forall M M1 M2 : PO,
       M1 = rotation I a M -> M2 = rotation J b M1 -> M2 = translation A B M)).
intros I J a b H; try assumption.
discrimine I J.
exists J; exists J; intros.
generalize
 (composee_rotations_meme_centre (I:=J) (A:=M) (B:=M1) (C:=M2) (a:=a) (b:=b));
 intros.
rewrite H3; auto.
apply rec_translation_vecteur; auto.
rewrite (deux_mes_angle_rotation J M (a:=a + b) (b:=0)); auto.
rewrite <- (rotation_angle_nul J M); auto.
Ringvec.
elim existence_rotation_Ia with (I := J) (M := I) (a := / 2 * b); intros C H7.
elim (rotation_def (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto; intros.
elim existence_rotation_Ia with (I := I) (M := J) (a := - (/ 2 * a));
 intros D H10.
elim (rotation_def (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto; intros.
cut (I <> D); intros.
cut (J <> C); intros.
cut (paralleles (droite I D) (droite J C)); intros.
elim (existence_projete_orthogonal (A:=J) (B:=C) I).
intros K H25; try assumption.
generalize (def_projete_orthogonal2 (A:=J) (B:=C) (C:=I) (H:=K)).
intros H60.
elim H60; auto; intros H61 H62; clear H60.
discrimine I K.
rewrite <- H9 in H61.
exists I; exists I; intros.
elim existence_reflexion_AB with (A := I) (B := D) (M := M);
 [ intros M' H16; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := I) (B := J) (M := M');
 [ intros N' H17; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := J) (B := I) (M := M1);
 [ intros N1 H19; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := J) (B := C) (M := N1);
 [ intros N2 H21; try clear existence_reflexion_AB | auto ].
generalize
 (composee_reflexions_axes_secants (A:=J) (B:=I) (C:=C) (M:=M1) (M':=N2)
    (M1:=N1) (a:=/ 2 * b)); intros H23.
generalize
 (composee_reflexions_axes_secants (A:=I) (B:=D) (C:=J) (M:=M) (M':=N')
    (M1:=M') (a:=/ 2 * a)); intros H24.
cut (M1 = N'); intros.
cut (N1 = M'); intros.
cut (M2 = N2); intros.
rewrite <- H15 in H21; rewrite H14 in H21; auto.
generalize (axe_reflexion_droite (A:=J) (B:=C) (C:=I) (M:=M') (M':=M2));
 intros.
generalize (axe_reflexion_droite (A:=I) (B:=J) (C:=D) (M:=M') (M':=M2));
 intros.
generalize (axe_reflexion_droite (A:=D) (B:=I) (C:=I) (M:=M') (M':=M2));
 intros.
rewrite H22; auto with geo.
generalize (reflexion_symetrie (A:=I) (B:=D) (M:=M) (M':=M')); intros.
rewrite <- H26; auto.
apply rec_translation_vecteur; auto.
Ringvec.
rewrite H20; auto.
apply paralleles_alignes3 with (3 := H8); auto.
rewrite H23; auto.
rewrite H12; auto.
apply deux_mes_angle_rotation.
replace (/ 2 * b + / 2 * b) with b; auto with real.
rewrite H13 in H19.
generalize (reflexion_symetrie (A:=I) (B:=J) (M:=M') (M':=N')); intros.
rewrite H14; auto.
generalize (axe_reflexion_droite (A:=J) (B:=I) (C:=I) (M:=N') (M':=N1));
 intros.
rewrite H15; auto with geo.
rewrite H24; auto.
rewrite H11; auto.
rewrite <- H9.
apply deux_mes_angle_rotation.
replace (/ 2 * a + / 2 * a) with a; auto with real.
rewrite <- (mes_oppx (A:=I) (B:=J) (C:=I) (D:=D) (x:=- (/ 2 * a))); auto.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
ring.
cut (orthogonal (vec I D) (vec I K)); intros.
elim existence_representant_vecteur with (A := K) (B := I) (C := D);
 intros L H28.
generalize (egalite_vecteur (A:=K) (B:=L) (C:=I) (D:=D)); intros.
cut (K <> L); intros.
elim existence_representant_vecteur with (A := K) (B := I) (C := K);
 intros P H31.
exists I; exists P; intros.
elim existence_reflexion_AB with (A := I) (B := D) (M := M);
 [ intros M' H16; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := I) (B := J) (M := M');
 [ intros N' H17; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := J) (B := I) (M := M1);
 [ intros N1 H19; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := J) (B := C) (M := N1);
 [ intros N2 H21; try clear existence_reflexion_AB | auto ].
generalize
 (composee_reflexions_axes_secants (A:=J) (B:=I) (C:=C) (M:=M1) (M':=N2)
    (M1:=N1) (a:=/ 2 * b)); intros H23.
generalize
 (composee_reflexions_axes_secants (A:=I) (B:=D) (C:=J) (M:=M) (M':=N')
    (M1:=M') (a:=/ 2 * a)); intros H24.
cut (M1 = N'); intros.
cut (N1 = M'); intros.
cut (M2 = N2); intros.
generalize
 (composee_reflexions_axes_paralleles (A:=I) (B:=D) (C:=K) (D:=L) (E:=P)
    (M:=M) (M':=M2) (M1:=M')); intros.
rewrite H26; auto.
apply rec_translation_vecteur; auto.
apply rec_translation_vecteur; auto.
rewrite <- H22 in H21; rewrite H20 in H21; auto.
elim (classic (L = J)); intros.
rewrite H27.
generalize (axe_reflexion_droite (A:=J) (B:=C) (C:=K) (M:=M') (M':=M2));
 intros.
rewrite <- H29; auto.
rewrite H27 in H13; auto.
generalize (axe_reflexion_droite (A:=J) (B:=C) (C:=L) (M:=M') (M':=M2));
 intros.
generalize (axe_reflexion_droite (A:=L) (B:=J) (C:=K) (M:=M') (M':=M2));
 intros.
rewrite <- H30; auto.
apply paralleles_alignes2 with (4 := H8); auto.
rewrite H29; auto.
apply paralleles_alignes1 with (3 := H28); auto.
rewrite H23; auto.
rewrite H15; auto.
apply deux_mes_angle_rotation.
replace (/ 2 * b + / 2 * b) with b; auto with real.
rewrite H18 in H19.
generalize (reflexion_symetrie (A:=I) (B:=J) (M:=M') (M':=N')); intros.
rewrite H20; auto.
generalize (axe_reflexion_droite (A:=J) (B:=I) (C:=I) (M:=N') (M':=N1));
 intros.
rewrite H22; auto with geo.
rewrite H24; auto.
rewrite H14; auto.
apply deux_mes_angle_rotation.
replace (/ 2 * a + / 2 * a) with a; auto with real.
rewrite <- (mes_oppx (A:=I) (B:=J) (C:=I) (D:=D) (x:=- (/ 2 * a))); auto.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
ring.
red in |- *; intros; apply H5.
apply vecteur_nul_conf; auto.
rewrite <- H28; rewrite <- H13; Ringvec.
elim (paralleles_vecteur (A:=I) (B:=D) (C:=J) (D:=C)); auto; intros.
replace (vec I D) with (add_PP (mult_PP x (vec J C)) (mult_PP 0 (vec J C))).
apply ortho_combinaison_lineaire.
apply def_orthogonal2.
replace (scalaire (vec J C) (vec I K)) with (- scalaire (vec J C) (vec K I)).
rewrite (def_orthogonal (A:=J) (B:=C) (C:=K) (D:=I)); auto.
ring.
replace (vec I K) with (mult_PP (-1) (vec K I)).
Simplscal.
Ringvec.
auto with geo.
rewrite H11; Ringvec.
try exact H6.
apply droites_paralleles_angle; auto.
unfold double_AV in |- *.
replace (cons_AV (vec I D) (vec J C)) with
 (plus (cons_AV (vec I D) (vec I J))
    (plus (cons_AV (vec I J) (vec J I)) (cons_AV (vec J I) (vec J C)))); 
 auto.
rewrite <- (mes_oppx (A:=I) (B:=J) (C:=I) (D:=D) (x:=- (/ 2 * a))); auto.
rewrite <- H2.
rewrite <- angle_plat.
repeat rewrite <- add_mes_compatible.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
replace (/ 2 * a + (pi + / 2 * b) + (/ 2 * a + (pi + / 2 * b))) with
 (/ 2 * a + / 2 * a + (/ 2 * b + / 2 * b) + (pi + pi)); 
 auto.
replace (/ 2 * a + / 2 * a) with a; auto with real.
replace (/ 2 * b + / 2 * b) with b; auto with real.
rewrite add_mes_compatible.
rewrite H.
replace (pi + pi) with deuxpi; auto.
rewrite pi_plus_pi.
repeat rewrite <- add_mes_compatible.
replace (0 + 0) with 0; auto.
ring.
ring.
ring.
try exact H0.
repeat rewrite Chasles; auto.
apply (image_distinct_centre (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto.
apply (image_distinct_centre (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto.
Qed.
 
Theorem composee_rotation_IJ_rotation :
 forall (I J : PO) (a b : R),
 image_angle (a + b) <> image_angle 0 ->
 ex
   (fun K : PO =>
    forall M M1 M2 : PO,
    M1 = rotation I a M -> M2 = rotation J b M1 -> M2 = rotation K (a + b) M).
intros I J a b H; try assumption.
discrimine I J.
exists I; intros.
generalize
 (composee_rotations_meme_centre (I:=J) (A:=M) (B:=M1) (C:=M2) (a:=a) (b:=b));
 intros.
rewrite H0; rewrite H3; auto.
elim existence_rotation_Ia with (I := J) (M := I) (a := / 2 * b); intros C H7.
elim existence_rotation_Ia with (I := I) (M := J) (a := - (/ 2 * a));
 intros D H10.
cut (I <> D); intros.
cut (J <> C); intros.
generalize
 (position_relative_droites_coplanaires (A:=I) (B:=D) (C:=J) (D:=C)); 
 intros.
elim H3; intros.
elim def_concours2 with (A := I) (B := D) (C := J) (D := C);
 [ intros K H27; try clear def_concours2; try exact H27
 | auto
 | auto
 | auto ].
elim H27; intros H28 H29; try clear H27; try exact H29.
exists K; intros.
elim existence_reflexion_AB with (A := I) (B := D) (M := M);
 [ intros M' H16; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := I) (B := J) (M := M');
 [ intros N' H17; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := J) (B := I) (M := M1);
 [ intros N1 H19; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := J) (B := C) (M := N1);
 [ intros N2 H21; try clear existence_reflexion_AB | auto ].
generalize
 (composee_reflexions_axes_secants (A:=J) (B:=I) (C:=C) (M:=M1) (M':=N2)
    (M1:=N1) (a:=/ 2 * b)); intros H23.
generalize
 (composee_reflexions_axes_secants (A:=I) (B:=D) (C:=J) (M:=M) (M':=N')
    (M1:=M') (a:=/ 2 * a)); intros H24.
cut (M1 = N'); intros.
cut (N1 = M'); intros.
cut (M2 = N2); intros.
elim (classic (I = K)); intros.
cut (J <> K); intros.
rewrite <- H12 in H29; rewrite <- H12.
elim (rotation_def (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto; intros.
cut (image_angle b = image_angle 0); intros.
cut (M2 = M1); intros.
rewrite H20; rewrite H5.
apply deux_mes_angle_rotation.
rewrite add_mes_compatible.
rewrite H18; rewrite <- add_mes_compatible.
replace (a + 0) with a; auto.
ring.
rewrite H6.
pattern M1 at 2 in |- *.
rewrite (rotation_angle_nul J M1).
apply deux_mes_angle_rotation; auto.
replace b with (/ 2 * b + / 2 * b); auto with real.
generalize (angle_alignes (A:=J) (B:=I) (C:=C)); intros H22; rewrite <- H22;
 auto with geo.
unfold double_AV in |- *.
rewrite <- H15.
rewrite add_mes_compatible; auto.
red in |- *; intros; apply H0.
rewrite H12; rewrite H13; auto.
elim (classic (J = K)); intros.
rewrite <- H13 in H28; rewrite <- H13.
elim (rotation_def (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto; intros.
cut (image_angle a = image_angle 0); intros.
cut (M1 = M); intros.
rewrite <- H20; rewrite H6.
apply deux_mes_angle_rotation.
rewrite add_mes_compatible.
rewrite H18; rewrite <- add_mes_compatible.
replace (0 + b) with b; try ring; auto.
rewrite (rotation_angle_nul I M).
rewrite H5.
apply deux_mes_angle_rotation; auto.
replace a with (/ 2 * a + / 2 * a); auto with real.
generalize (angle_alignes (A:=I) (B:=D) (C:=J)); intros H22; rewrite <- H22;
 auto.
unfold double_AV in |- *.
rewrite <- (mes_oppx (A:=I) (B:=J) (C:=I) (D:=D) (x:=- (/ 2 * a))); auto.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
rewrite add_mes_compatible; auto.
ring.
mesure I K J K.
cut
 (plus (cons_AV (vec I K) (vec J K)) (cons_AV (vec I K) (vec J K)) =
  image_angle (a + b)); intros.
generalize
 (composee_reflexions_axes_secants (A:=K) (B:=I) (C:=J) (M:=M) (M':=M2)
    (M1:=M') (a:=x)); intros.
rewrite H18; auto.
apply deux_mes_angle_rotation.
rewrite add_mes_compatible.
rewrite H14; rewrite H15; auto.
rewrite angle_oppu_oppv; auto.
generalize (axe_reflexion_droite (A:=I) (B:=D) (C:=K) (M:=M) (M':=M'));
 intros.
rewrite H20; auto.
generalize (axe_reflexion_droite (A:=J) (B:=C) (C:=K) (M:=N1) (M':=N2));
 intros.
rewrite H11; rewrite H20; auto; rewrite H9; auto.
replace (plus (cons_AV (vec I K) (vec J K)) (cons_AV (vec I K) (vec J K)))
 with (double_AV (cons_AV (vec I K) (vec J K))); auto.
generalize (alignement_et_angles (A:=I) (B:=D) (C:=K) (D:=J) (E:=C) (F:=K));
 intros.
rewrite <- H15; auto.
unfold double_AV in |- *.
replace (cons_AV (vec I D) (vec J C)) with
 (plus (cons_AV (vec I D) (vec I J))
    (plus (cons_AV (vec I J) (vec J I)) (cons_AV (vec J I) (vec J C)))); 
 auto.
rewrite <- angle_plat; auto.
elim (rotation_def (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto; intros.
elim (rotation_def (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto; intros.
rewrite <- H25.
rewrite <- (mes_oppx (A:=I) (B:=J) (C:=I) (D:=D) (x:=- (/ 2 * a))); auto.
repeat rewrite <- add_mes_compatible.
replace (- - (/ 2 * a)) with (/ 2 * a).
replace (/ 2 * a + (pi + / 2 * b) + (/ 2 * a + (pi + / 2 * b))) with
 (/ 2 * a + / 2 * a + (/ 2 * b + / 2 * b) + (pi + pi)).
replace (/ 2 * a + / 2 * a) with a; auto with real.
replace (/ 2 * b + / 2 * b) with b; auto with real.
replace (pi + pi) with deuxpi; auto.
rewrite add_mes_compatible.
rewrite pi_plus_pi.
repeat rewrite <- add_mes_compatible.
replace (a + b + 0) with (a + b); auto.
ring.
ring.
ring.
repeat rewrite Chasles; auto.
rewrite H6; rewrite H23; auto.
apply deux_mes_angle_rotation.
replace (/ 2 * b + / 2 * b) with b; auto with real.
elim (rotation_def (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto; intros.
rewrite <- H8 in H17.
generalize (reflexion_symetrie (A:=I) (B:=J) (M:=M') (M':=M1)); intros.
rewrite H9; auto.
generalize (axe_reflexion_droite (A:=J) (B:=I) (C:=I) (M:=M1) (M':=N1));
 intros.
rewrite H11; auto with geo.
rewrite H5; rewrite H24; auto.
apply deux_mes_angle_rotation.
replace (/ 2 * a + / 2 * a) with a; auto with real.
elim (rotation_def (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto; intros.
rewrite <- (mes_oppx (A:=I) (B:=J) (C:=I) (D:=D) (x:=- (/ 2 * a))); auto.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
ring.
absurd (paralleles (droite J C) (droite I D)); auto with geo.
cut (double_AV (cons_AV (vec I D) (vec J C)) = image_angle (a + b)); intros.
apply angle_non_paralleles; auto.
red in |- *; intros; apply H.
rewrite <- H6; auto.
rewrite add_mes_compatible; auto.
unfold double_AV in |- *.
replace (cons_AV (vec I D) (vec J C)) with
 (plus (cons_AV (vec I D) (vec I J))
    (plus (cons_AV (vec I J) (vec J I)) (cons_AV (vec J I) (vec J C)))); 
 auto.
rewrite <- angle_plat; auto.
elim (rotation_def (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto; intros.
elim (rotation_def (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto; intros.
rewrite <- H9.
rewrite <- (mes_oppx (A:=I) (B:=J) (C:=I) (D:=D) (x:=- (/ 2 * a))); auto.
repeat rewrite <- add_mes_compatible.
replace (- - (/ 2 * a)) with (/ 2 * a).
replace (/ 2 * a + (pi + / 2 * b) + (/ 2 * a + (pi + / 2 * b))) with
 (/ 2 * a + / 2 * a + (/ 2 * b + / 2 * b) + (pi + pi)).
replace (/ 2 * a + / 2 * a) with a; auto with real.
replace (/ 2 * b + / 2 * b) with b; auto with real.
replace (pi + pi) with deuxpi; auto.
rewrite add_mes_compatible.
rewrite pi_plus_pi.
repeat rewrite <- add_mes_compatible.
replace (a + b + 0) with (a + b); auto.
ring.
ring.
ring.
repeat rewrite Chasles; auto.
apply (image_distinct_centre (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto.
apply (image_distinct_centre (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto.
apply geometrie_plane; auto.
apply (image_distinct_centre (I:=J) (A:=I) (B:=C) (a:=/ 2 * b)); auto.
apply (image_distinct_centre (I:=I) (A:=J) (B:=D) (a:=- (/ 2 * a))); auto.
Qed.
 
Theorem translation_reflexion_axe_parallele_commutent :
 forall A B C D M M1 M2 N1 N2 : PO,
 A <> B ->
 C <> D ->
 paralleles (droite A B) (droite C D) ->
 M1 = translation A B M ->
 M2 = reflexion C D M1 ->
 N1 = reflexion C D M -> N2 = translation A B N1 -> N2 = M2.
intros A B C D M M1 M2 N1 N2 H H0 H1 H2 H3 H4 H5; try assumption.
rewrite H3.
cut (vec M M1 = vec A B).
intros H100.
cut (vec N1 N2 = vec A B).
intros H102.
cut (vec M M1 = vec N1 N2); intros.
elim (paralleles_vecteur (A:=C) (B:=D) (C:=A) (D:=B)); intros; auto with geo.
cut (x <> 0); intros.
elim (classic (alignes C D M)); intros.
generalize (reflexion_axe (A:=C) (B:=D) (M:=M)); intros.
cut (N1 = M); intros.
rewrite H11 in H6.
cut (alignes C D M1); intros.
generalize (reflexion_axe (A:=C) (B:=D) (M:=M1)); intros.
rewrite <- H13; auto.
apply conversion_PP with (a := 1) (b := 1); auto.
RingPP2 H6; Ringvec.
auto with real.
halignes H9 ipattern:x0.
apply colineaire_alignes with (x0 + / x).
replace (vec C M1) with (add_PP (vec C M) (vec M M1)).
rewrite H12.
rewrite <- (translation_vecteur H2).
replace (vec A B) with (mult_PP (/ x) (vec C D)).
Ringvec.
rewrite H7.
replace (mult_PP (/ x) (mult_PP x (vec A B))) with
 (mult_PP (/ x * x) (vec A B)).
replace (/ x * x) with 1; auto with real.
Ringvec.
Ringvec.
Ringvec.
rewrite H10; auto.
elim (existence_projete_orthogonal (A:=C) (B:=D) M); auto; intros K H10.
elim existence_representant_vecteur with (A := K) (B := A) (C := B);
 intros L H11.
generalize (reflexion_def (A:=C) (B:=D) (M:=M) (M':=N1) (H:=K)); intros H12.
cut (L = milieu M1 N2); intros.
generalize (reflexion_axe_orthogonal_segment (A:=C) (B:=D) (M:=M) (M':=N1));
 intros.
generalize
 (paralleles_orthogonal (A:=M) (B:=N1) (C:=M1) (D:=N2) (E:=C) (F:=D)); 
 intros.
apply reflexion_def2 with L; auto.
elim (def_projete_orthogonal2 (A:=C) (B:=D) (C:=M) (H:=K)); auto; intros.
apply def_projete_orthogonal; auto.
apply (paralleles_alignes1 (A:=A) (B:=B) (C:=C) (D:=D) (E:=K) (F:=L)); auto.
replace (vec L M1) with (vec K M); auto.
apply egalite_vecteur.
rewrite H11; auto with geo.
apply milieu_vecteur_double; auto.
apply vecteur_milieu.
replace (vec M1 N2) with (vec M N1); auto with geo.
rewrite H12; auto.
cut (2 <> 0); intros; auto with real.
replace (mult_PP (/ 2) (mult_PP 2 (vec M K))) with (vec M K); auto.
replace (vec M1 L) with (vec M K); auto.
apply egalite_vecteur; auto.
rewrite H11; auto.
Fieldvec 2.
red in |- *; intros; apply H0.
apply vecteur_nul_conf.
rewrite H7; rewrite H8; Ringvec.
rewrite H100; auto.
symmetry  in |- *.
apply translation_vecteur; auto.
symmetry  in |- *.
apply translation_vecteur; auto.
Qed.