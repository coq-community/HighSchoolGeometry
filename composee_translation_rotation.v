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


Require Export composee_reflexions.
Set Implicit Arguments.
Unset Strict Implicit.
 
Theorem composee_translation_rotation :
 forall (I A B : PO) (a : R),
 image_angle a <> image_angle 0 ->
 exists J : PO,
   (forall M M1 M2 : PO,
    M1 = translation A B M -> M2 = rotation I a M1 -> M2 = rotation J a M).
intros I A B a H50; try assumption.
elim (classic (A = B)); intros H2.
exists I; intros.
generalize (translation_vecteur (I:=A) (J:=B) (A:=M) (A':=M1)); intros.
cut (M1 = M); intros.
rewrite H3 in H0; auto.
symmetry  in |- *.
apply vecteur_nul_conf.
rewrite <- H1; auto.
rewrite <- H2; Ringvec.
elim existence_representant_vecteur with (A := I) (B := milieu A B) (C := A);
 intros D H3; try clear existence_representant_vecteur; 
 try exact H3.
cut (vec A B = mult_PP 2 (mult_PP (/ 2) (vec A B))); intros.
cut (I <> D); intros.
elim existence_rotation_Ia with (I := I) (M := D) (a := pisurdeux);
 intros C H7.
cut (I <> C); auto; intros.
cut (orthogonal (vec I C) (vec I D)); intros.
elim existence_representant_vecteur with (A := C) (B := I) (C := D);
 intros E H10; try clear existence_representant_vecteur; 
 try exact H10.
generalize (egalite_vecteur (A:=C) (B:=E) (C:=I) (D:=D)).
intros H33.
elim existence_representant_vecteur with (A := D) (B := A) (C := B);
 intros F H11; try clear existence_representant_vecteur; 
 try exact H11.
cut (D <> E); intros.
cut (paralleles (droite I C) (droite D E)); intros.
elim existence_rotation_Ia with (I := I) (M := C) (a := / 2 * a);
 intros G H18.
cut (I <> G); intros.
generalize (rotation_def (I:=I) (A:=C) (B:=G) (a:=/ 2 * a)); intros.
generalize
 (position_relative_droites_coplanaires (A:=D) (B:=E) (C:=I) (D:=G)); 
 intros.
elim H12; intros; auto with geo.
elim def_concours2 with (A := D) (B := E) (C := I) (D := G);
 [ intros J H27; try clear def_concours2; try exact H27
 | auto
 | auto
 | auto ].
elim H27; intros H28 H29; try clear H27; try exact H29.
cut (J <> I); intros.
exists J; intros.
generalize (translation_vecteur (I:=A) (J:=B) (A:=M) (A':=M1)); intros.
elim existence_reflexion_AB with (A := D) (B := E) (M := M);
 [ intros M' H23; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := I) (B := C) (M := M');
 [ intros N H24; try clear existence_reflexion_AB | auto ].
generalize
 (composee_reflexions_axes_paralleles (A:=D) (B:=E) (C:=I) (D:=C) (E:=F)
    (M:=M) (M':=N) (M1:=M')); intros.
cut (N = translation D F M); intros.
cut (M1 = N); intros.
elim existence_reflexion_AB with (A := I) (B := C) (M := M1);
 [ intros N' H31; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := I) (B := G) (M := N');
 [ intros N1 H32; try clear existence_reflexion_AB | auto ].
generalize (reflexion_symetrie (A:=I) (B:=C) (M:=M') (M':=N)); intros.
rewrite H21 in H31.
cut (N' = M'); intros.
generalize
 (composee_reflexions_axes_secants (A:=I) (B:=C) (C:=G) (M:=N) (M':=N1)
    (M1:=N') (a:=/ 2 * a)); intros.
rewrite H16.
rewrite H21.
replace a with (/ 2 * a + / 2 * a); auto.
rewrite <- H26; auto.
elim H9; intros.
cut (D <> J \/ E <> J); intros.
elim H34;
 [ intros H35; try clear H34 | intros H35; try clear H34; try exact H35 ].
mesure J D J I.
cut (double_AV (cons_AV (vec J D) (vec J I)) = image_angle a); intros.
generalize (axe_reflexion_droite (A:=D) (B:=E) (C:=J) (M:=M) (M':=M'));
 intros.
generalize (axe_reflexion_droite (A:=I) (B:=G) (C:=J) (M:=M') (M':=N1));
 intros.
generalize
 (composee_reflexions_axes_secants (A:=J) (B:=D) (C:=I) (M:=M) (M':=N1)
    (M1:=M') (a:=x)); intros.
rewrite H39; auto.
apply deux_mes_angle_rotation.
rewrite add_mes_compatible.
unfold double_AV in H36.
rewrite H34; rewrite H36.
replace (/ 2 * a + / 2 * a) with a; auto with real.
apply (axe_reflexion_droite (A:=I) (B:=G) (C:=J) (M:=M') (M':=N1)); auto.
rewrite H32; rewrite H25; auto.
rewrite
 (angles_et_paralleles (A:=J) (B:=D) (C:=J) (D:=I) (E:=I) (F:=C) (G:=I)
    (I:=G)).
unfold double_AV in |- *; rewrite <- H30.
rewrite <- add_mes_compatible.
replace (/ 2 * a + / 2 * a) with a; auto with real.
auto.
red in |- *; intros.
rewrite H36 in H28.
absurd (alignes D E I); auto.
auto.
auto.
generalize (alignes_paralleles (A:=D) (B:=E) (C:=J)); intros.
apply paralleles_trans with (C := D) (D := E); auto with geo.
apply paralleles_trans with (C := D) (D := J); auto with geo.
generalize (alignes_paralleles (A:=I) (B:=G) (C:=J)); intros.
apply paralleles_trans with (C := I) (D := J); auto with geo.
mesure J E J I.
cut
 (plus (cons_AV (vec J E) (vec J I)) (cons_AV (vec J E) (vec J I)) =
  image_angle a); intros.
generalize (axe_reflexion_droite (A:=E) (B:=D) (C:=J) (M:=M) (M':=M'));
 intros.
generalize (axe_reflexion_droite (A:=I) (B:=G) (C:=J) (M:=M') (M':=N1));
 intros.
generalize
 (composee_reflexions_axes_secants (A:=J) (B:=E) (C:=I) (M:=M) (M':=N1)
    (M1:=M') (a:=x)); intros.
rewrite H39; auto.
apply deux_mes_angle_rotation.
rewrite add_mes_compatible.
unfold double_AV in H36.
rewrite H34; rewrite H36.
replace (/ 2 * a + / 2 * a) with a; auto with real.
apply (axe_reflexion_droite (A:=E) (B:=D) (C:=J) (M:=M) (M':=M'));
 auto with geo.
apply (axe_reflexion_droite (A:=D) (B:=E) (C:=E) (M:=M) (M':=M'));
 auto with geo.
apply (axe_reflexion_droite (A:=I) (B:=G) (C:=J) (M:=M') (M':=N1));
 auto with geo.
rewrite H32; rewrite H25; auto.
replace (plus (cons_AV (vec J E) (vec J I)) (cons_AV (vec J E) (vec J I)))
 with (double_AV (cons_AV (vec J E) (vec J I))); auto.
rewrite
 (angles_et_paralleles (A:=J) (B:=E) (C:=J) (D:=I) (E:=I) (F:=C) (G:=I)
    (I:=G)).
unfold double_AV in |- *.
rewrite <- H30.
rewrite <- add_mes_compatible.
replace (/ 2 * a + / 2 * a) with a; auto with real.
auto.
auto.
auto.
auto.
generalize (alignes_paralleles (A:=E) (B:=D) (C:=J)); intros.
apply paralleles_trans with (C := D) (D := E); auto with geo.
apply paralleles_trans with (C := E) (D := D); auto with geo.
apply paralleles_trans with (C := E) (D := J); auto with geo.
generalize (alignes_paralleles (A:=I) (B:=G) (C:=J)); intros.
apply paralleles_trans with (C := I) (D := J); auto with geo.
apply not_and_or.
red in |- *; intros.
elim H34; intros.
apply H5.
rewrite H36; rewrite H35; auto.
auto.
auto.
elim H9; intros; auto with real.
auto with real.
rewrite H22; auto.
rewrite H20.
apply rec_translation_vecteur.
rewrite <- H17; auto.
apply H19; auto.
replace (vec D E) with (vec I C).
apply ortho_sym; auto with geo.
apply egalite_vecteur; auto with geo.
apply rec_translation_vecteur.
apply egalite_vecteur; auto with geo.
replace (vec D I) with (mult_PP (-1) (vec I D)).
rewrite <- H10; Ringvec.
Ringvec.
apply rec_translation_vecteur.
replace (vec D I) with (mult_PP (-1) (vec I D)).
replace (vec I F) with (add_PP (vec I D) (vec D F)).
rewrite H11; rewrite H3; auto.
rewrite (milieu_vecteur_double (A:=A) (B:=B) (M:=milieu A B)); auto.
Ringvec.
Ringvec.
Ringvec.
red in |- *; intros.
rewrite H14 in H28.
absurd (alignes D E I); auto.
apply orthogonal_non_alignes; auto.
replace (vec D E) with (vec I C); auto with geo.
absurd (paralleles (droite D E) (droite I G)); auto with geo.
generalize (angle_non_paralleles (A:=I) (B:=C) (C:=I) (D:=G)); intros.
apply non_paralleles_trans with (A := I) (B := C); auto with geo.
red in |- *; intros.
apply H14; auto with geo.
elim H9; auto; intros.
unfold double_AV in |- *; rewrite <- H17.
rewrite <- add_mes_compatible.
replace (/ 2 * a + / 2 * a) with a; auto with real.
apply image_distinct_centre with (2 := H18); auto with geo.
apply (colineaires_paralleles (k:=1) (A:=I) (B:=C) (C:=D) (D:=E)); auto.
replace (vec D E) with (vec I C); auto with geo.
Ringvec.
red in |- *; intros; apply H1.
symmetry  in |- *.
apply vecteur_nul_conf; auto.
rewrite H33; auto.
rewrite H5; Ringvec.
elim (rotation_def (I:=I) (A:=D) (B:=C) (a:=pisurdeux)); auto with geo;
 intros.
apply image_distinct_centre with (2 := H7); auto.
red in |- *; intros; apply H2.
apply vecteur_nul_conf; auto.
rewrite (milieu_vecteur_double (A:=A) (B:=B) (M:=milieu A B)); auto.
replace (vec A (milieu A B)) with (mult_PP (-1) (vec (milieu A B) A)).
rewrite <- H3; rewrite H0; auto.
Ringvec.
Ringvec.
cut (2 <> 0); intros; auto with real.
Fieldvec 2.
Qed.
 
Theorem composee_rotation_translation :
 forall (I A B : PO) (a : R),
 image_angle a <> image_angle 0 ->
 ex
   (fun J : PO =>
    forall M M1 M2 : PO,
    M1 = rotation I a M -> M2 = translation A B M1 -> M2 = rotation J a M).
intros I A B a H50; try assumption.
elim (classic (A = B)); intros H2.
exists I; intros.
generalize (translation_vecteur (I:=A) (J:=B) (A:=M1) (A':=M2)); intros.
cut (M1 = M2); intros.
rewrite H3 in H; auto.
apply vecteur_nul_conf.
rewrite <- H1; auto.
rewrite <- H2; Ringvec.
elim existence_representant_vecteur with (A := I) (B := milieu A B) (C := B);
 intros D H3; try clear existence_representant_vecteur; 
 try exact H3.
cut (vec A B = mult_PP 2 (mult_PP (/ 2) (vec A B))); intros.
cut (I <> D); intros.
elim existence_rotation_Ia with (I := I) (M := D) (a := pisurdeux);
 intros C H7.
cut (I <> C); auto with geo; intros.
cut (orthogonal (vec I C) (vec I D)); intros.
elim existence_representant_vecteur with (A := C) (B := I) (C := D);
 intros E H10; try clear existence_representant_vecteur; 
 try exact H10.
generalize (egalite_vecteur (A:=C) (B:=E) (C:=I) (D:=D)).
intros H33.
elim existence_representant_vecteur with (A := I) (B := A) (C := B);
 intros F H11; try clear existence_representant_vecteur; 
 try exact H11.
cut (D <> E); intros.
cut (paralleles (droite I C) (droite D E)); intros.
elim existence_rotation_Ia with (I := I) (M := C) (a := - (/ 2 * a));
 intros G H18.
cut (I <> G); intros.
generalize (rotation_def (I:=I) (A:=C) (B:=G) (a:=- (/ 2 * a))); intros.
generalize
 (position_relative_droites_coplanaires (A:=D) (B:=E) (C:=I) (D:=G)); 
 intros.
elim H12; intros; auto with geo.
elim def_concours2 with (A := D) (B := E) (C := I) (D := G);
 [ intros J H28; try clear def_concours2; try exact H28
 | auto
 | auto
 | auto ].
elim H28; intros.
clear H28.
cut (J <> I); intros.
exists J; intros.
generalize (translation_vecteur (I:=A) (J:=B) (A:=M1) (A':=M2)); intros.
elim existence_reflexion_AB with (A := I) (B := G) (M := M);
 [ intros N' H25; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := I) (B := C) (M := N');
 [ intros N1 H26; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := I) (B := C) (M := M1);
 [ intros M' H27; try clear existence_reflexion_AB | auto ].
elim existence_reflexion_AB with (A := D) (B := E) (M := M');
 [ intros N H29; try clear existence_reflexion_AB | auto ].
generalize
 (composee_reflexions_axes_paralleles (A:=I) (B:=C) (C:=D) (D:=E) (E:=F)
    (M:=M1) (M':=N) (M1:=M')); intros.
cut (N = translation I F M1); intros.
cut (M1 = N1); intros.
cut (M2 = N); intros.
generalize (reflexion_symetrie (A:=I) (B:=C) (M:=N') (M':=N1)); intros.
rewrite H23 in H27.
cut (N' = M'); intros.
generalize
 (composee_reflexions_axes_secants (A:=I) (B:=G) (C:=C) (M:=M) (M':=M1)
    (M1:=N') (a:=/ 2 * a)); intros.
elim H9; auto; intros.
rewrite H24.
cut (D <> J \/ E <> J); intros.
elim H35; intros.
mesure J I J D.
cut
 (plus (cons_AV (vec J I) (vec J D)) (cons_AV (vec J I) (vec J D)) =
  image_angle a); intros.
generalize (axe_reflexion_droite (A:=I) (B:=G) (C:=J) (M:=M) (M':=N'));
 intros.
generalize (axe_reflexion_droite (A:=D) (B:=E) (C:=J) (M:=N') (M':=N));
 intros.
generalize
 (composee_reflexions_axes_secants (A:=J) (B:=I) (C:=D) (M:=M) (M':=N)
    (M1:=N') (a:=x)); intros.
rewrite H41; auto.
apply deux_mes_angle_rotation.
rewrite add_mes_compatible.
rewrite H37; rewrite H38; auto.
rewrite H40; auto.
rewrite H30; rewrite H29; auto.
replace (plus (cons_AV (vec J I) (vec J D)) (cons_AV (vec J I) (vec J D)))
 with (double_AV (cons_AV (vec J I) (vec J D))); auto.
rewrite
 (angles_et_paralleles (A:=J) (B:=I) (C:=J) (D:=D) (E:=I) (F:=G) (G:=I)
    (I:=C)); auto.
unfold double_AV in |- *.
rewrite <- (mes_oppx (A:=I) (B:=C) (C:=I) (D:=G) (x:=- (/ 2 * a))); auto.
rewrite <- add_mes_compatible.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
replace (/ 2 * a + / 2 * a) with a; auto with real.
ring.
generalize (alignes_paralleles (A:=I) (B:=G) (C:=J)); intros.
apply paralleles_trans with (C := I) (D := J); auto with geo.
generalize (alignes_paralleles (A:=D) (B:=E) (C:=J)); intros.
apply paralleles_trans with (C := D) (D := E); auto.
apply paralleles_trans with (C := D) (D := J); auto with geo.
mesure J I J E.
cut
 (plus (cons_AV (vec J I) (vec J E)) (cons_AV (vec J I) (vec J E)) =
  image_angle a); intros.
generalize (axe_reflexion_droite (A:=I) (B:=G) (C:=J) (M:=M) (M':=N'));
 intros.
generalize (axe_reflexion_droite (A:=E) (B:=D) (C:=J) (M:=N') (M':=N));
 intros.
generalize
 (composee_reflexions_axes_secants (A:=J) (B:=I) (C:=E) (M:=M) (M':=N)
    (M1:=N') (a:=x)); intros.
rewrite H41; auto.
apply deux_mes_angle_rotation.
rewrite add_mes_compatible.
rewrite H37; rewrite H38; auto.
rewrite H40; auto with geo.
apply (axe_reflexion_droite (A:=D) (B:=E) (C:=E) (M:=N') (M':=N));
 auto with geo.
rewrite H29; rewrite H30; auto.
replace (plus (cons_AV (vec J I) (vec J E)) (cons_AV (vec J I) (vec J E)))
 with (double_AV (cons_AV (vec J I) (vec J E))); auto.
rewrite
 (angles_et_paralleles (A:=J) (B:=I) (C:=J) (D:=E) (E:=I) (F:=G) (G:=I)
    (I:=C)); auto.
unfold double_AV in |- *.
rewrite <- (mes_oppx (A:=I) (B:=C) (C:=I) (D:=G) (x:=- (/ 2 * a))); auto.
rewrite <- add_mes_compatible.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
replace (/ 2 * a + / 2 * a) with a; auto with real.
ring.
generalize (alignes_paralleles (A:=I) (B:=G) (C:=J)); intros.
apply paralleles_trans with (C := I) (D := J); auto with geo.
generalize (alignes_paralleles (A:=E) (B:=D) (C:=J)); intros.
apply paralleles_trans with (C := D) (D := E); auto.
apply paralleles_trans with (C := E) (D := D); auto with geo.
apply paralleles_trans with (C := E) (D := J); auto with geo.
apply not_and_or.
red in |- *; intros.
elim H35; intros.
apply H5.
rewrite H36; rewrite H37; auto.
rewrite H28; auto.
rewrite H21; auto.
apply rec_translation_vecteur.
rewrite H11; auto.
apply rec_translation_vecteur; auto with geo.
apply rec_translation_vecteur; auto with geo.
replace (vec D F) with (add_PP (vec I F) (mult_PP (-1) (vec I D))).
rewrite H11; rewrite H3; auto.
rewrite (milieu_vecteur_double (A:=A) (B:=B) (M:=milieu A B)); auto.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=milieu A B)); auto.
Ringvec.
Ringvec.
generalize
 (composee_reflexions_axes_secants (A:=I) (B:=G) (C:=C) (M:=M) (M':=N1)
    (M1:=N') (a:=/ 2 * a)); intros.
rewrite H17; rewrite H23; auto.
replace (/ 2 * a + / 2 * a) with a; auto with real.
rewrite <- (mes_oppx (A:=I) (B:=C) (C:=I) (D:=G) (x:=- (/ 2 * a))); auto.
replace (- - (/ 2 * a)) with (/ 2 * a); auto.
ring.
elim H9; auto.
apply H21; auto.
apply rec_translation_vecteur; auto with geo.
apply rec_translation_vecteur; auto with geo.
replace (vec D F) with (add_PP (vec I F) (mult_PP (-1) (vec I D))).
rewrite H11; rewrite H3; auto.
rewrite (milieu_vecteur_double (A:=A) (B:=B) (M:=milieu A B)); auto.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=milieu A B)); auto.
Ringvec.
Ringvec.
red in |- *; intros.
rewrite H16 in H14.
absurd (alignes D E I); auto.
apply orthogonal_non_alignes; auto with geo.
replace (vec D E) with (vec I C); auto with geo.
absurd (paralleles (droite D E) (droite I G)); auto.
generalize (angle_non_paralleles (A:=I) (B:=G) (C:=I) (D:=C)); intros H31.
apply non_paralleles_trans with (A := I) (B := C); auto with geo.
red in |- *; intros.
apply H31; auto.
elim H9; auto; intros.
unfold double_AV in |- *.
rewrite <- (mes_oppx (A:=I) (B:=C) (C:=I) (D:=G) (x:=- (/ 2 * a))); auto.
rewrite <- add_mes_compatible.
replace (- - (/ 2 * a)) with (/ 2 * a); auto with geo.
replace (/ 2 * a + / 2 * a) with a; auto with real.
ring.
apply image_distinct_centre with (2 := H18); auto.
apply (colineaires_paralleles (k:=1) (A:=I) (B:=C) (C:=D) (D:=E)); auto.
replace (vec D E) with (vec I C); auto with geo.
Ringvec.
red in |- *; intros; apply H1.
symmetry  in |- *.
apply vecteur_nul_conf; auto.
rewrite H33; auto.
rewrite H5; Ringvec.
elim (rotation_def (I:=I) (A:=D) (B:=C) (a:=pisurdeux)); auto with geo;
 intros.
apply image_distinct_centre with (2 := H7); auto with geo.
red in |- *; intros; apply H2.
apply vecteur_nul_conf; auto.
replace (vec A B) with (mult_PP 2 (vec (milieu A B) B)).
rewrite <- H3.
rewrite H0.
Ringvec.
rewrite (milieu_vecteur_double (A:=A) (B:=B) (M:=milieu A B)); auto.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=milieu A B)); auto.
cut (2 <> 0); intros; auto with real.
Fieldvec 2.
Qed.