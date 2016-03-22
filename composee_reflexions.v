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


Require Export reflexion_plane.
Require Export dilatations.
Require Export rotation_plane.
Set Implicit Arguments.
Unset Strict Implicit.
 
Theorem composee_reflexions_axes_paralleles :
 forall A B C D E M M' M1 : PO,
 A <> B ->
 A <> C ->
 orthogonal (vec A B) (vec A C) ->
 D = translation A B C ->
 E = translation A C C ->
 M1 = reflexion A B M -> M' = reflexion C D M1 -> M' = translation A E M.
intros A B C D E M M' M1 H11 H0 H6 H2 H3 H4 H5; try assumption.
generalize (translation_vecteur (I:=A) (J:=C) (A:=C) (A':=E)); intros H21.
generalize (translation_vecteur (I:=A) (J:=B) (A:=C) (A':=D)); intros H22.
cut (C <> D).
intros H7.
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H8; try clear existence_projete_orthogonal; try exact H8 | auto ].
elim existence_projete_orthogonal with (A := C) (B := D) (C := M1);
 [ intros H1 H12; try clear existence_projete_orthogonal | auto ].
elim def_projete_orthogonal2 with (A := A) (B := B) (C := M) (H := H);
 [ intros | auto | auto ].
elim def_projete_orthogonal2 with (A := C) (B := D) (C := M1) (H := H1);
 [ intros | auto | auto ].
apply rec_translation_vecteur.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M1) (H:=H));
 intros.
generalize
 (reflexion_projete_orthogonal_milieu (A:=C) (B:=D) (M:=M1) (M':=M') (H:=H1));
 intros.
replace (vec M M') with (add_PP (vec M M1) (vec M1 M')).
rewrite (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M1) (H:=H)); auto.
rewrite (reflexion_def (A:=C) (B:=D) (M:=M1) (M':=M') (H:=H1)); auto.
rewrite (milieu_vecteur (A:=M) (B:=M1) (M:=H)); auto.
replace (add_PP (mult_PP 2 (vec H M1)) (mult_PP 2 (vec M1 H1))) with
 (mult_PP 2 (add_PP (vec H M1) (vec M1 H1))).
replace (add_PP (vec H M1) (vec M1 H1)) with (vec H H1).
cut (vec H H1 = vec A C); intros.
rewrite H17.
generalize (translation_vecteur (I:=A) (J:=C) (A:=C) (A':=E)); intros.
replace (vec A E) with (add_PP (vec A C) (vec C E)).
rewrite H18; auto.
Ringvec.
Ringvec.
generalize (triangle_rectangle_repere (O:=A) (I:=B) (J:=C)); intros.
halignes H9 ipattern:k.
halignes H13 ipattern:k0.
elim (classic (k = 0)); intros.
cut (A = H); intros.
generalize (translation_bipoint (I:=A) (J:=B) (A:=A) (A':=B) (B:=C) (B':=D));
 intros.
cut (B <> D); intros.
cut (orthogonal (vec B A) (vec B D)); intros.
generalize (triangle_rectangle_repere (O:=B) (I:=A) (J:=D)); intros.
rewrite H24; auto with geo.
elim orthogonal_paralleles with (A := B) (B := A) (C := D) (E := H) (F := H1);
 [ intros k1 H28; try clear orthogonal_paralleles
 | auto
 | auto
 | auto
 | auto ].
rewrite
 (couple_colineaires_parallelogramme (A:=B) (B:=H) (C:=D) (D:=H1)
    (k:=1 + - k0) (k':=k1)); auto.
unfold not in |- *; intros; apply H11.
rewrite H29; rewrite H23; auto.
rewrite <- H23.
auto with geo.
replace (vec D H1) with (add_PP (mult_PP (-1) (vec C D)) (vec C H1)).
rewrite H19.
rewrite <- H23.
rewrite <- H22; auto.
Ringvec.
Ringvec.
cut (orthogonal (vec H H1) (vec A B)); intros; auto with geo.
replace (vec H H1) with (add_PP (vec H M) (vec M H1)).
apply ortho_somme; auto with geo.
replace (vec M H1) with
 (add_PP (mult_PP 1 (vec M M1)) (mult_PP (-1) (vec H1 M1))).
Simplortho.
replace (vec M M1) with
 (add_PP (mult_PP (-1) (vec H M)) (mult_PP 1 (vec H M1))).
Simplortho.
rewrite <- (milieu_vecteur (A:=M) (B:=M1) (M:=H)); auto with geo.
Ringvec.
rewrite H22; auto with geo.
Ringvec.
Ringvec.
rewrite <- H24; auto with geo.
unfold not in |- *; intros; apply H0.
cut (vec A C = vec B D); auto with geo; intros.
rewrite H25 in H26.
apply conversion_PP with (a := 1) (b := 1); auto.
RingPP2 H26.
Ringvec.
discrR.
apply conversion_PP with (a := 1) (b := 1); auto.
RingPP2 H18.
rewrite H20.
Ringvec.
discrR.
elim orthogonal_paralleles with (A := A) (B := B) (C := C) (E := H) (F := H1);
 [ intros k1 H23; try clear orthogonal_paralleles; try exact H23
 | auto
 | auto
 | auto
 | auto ].
rewrite <- H22 in H19; auto.
cut (vec A B = mult_PP (/ k) (vec A H)); intros; auto with geo.
rewrite H24 in H19.
rewrite
 (couple_colineaires_parallelogramme (A:=A) (B:=H) (C:=C) (D:=H1)
    (k:=k0 * / k) (k':=k1)); auto.
unfold not in |- *; intros; apply H20.
rewrite <- H25 in H18; auto.
elim produit_vecteur_nul with (a := k) (A := A) (B := B);
 [ intros H26; try clear produit_vecteur_nul; try exact H26
 | intros H26; try clear produit_vecteur_nul
 | try clear produit_vecteur_nul ].
absurd (A = B); auto.
rewrite <- H18; Ringvec.
apply alignes_non_alignes_trans with B; auto with geo.
apply distinct_produit_vecteur with (3 := H18); auto.
rewrite H19; Ringvec.
rewrite H18.
Fieldvec k.
cut (vec A H1 = add_PP (mult_PP k0 (vec A B)) (mult_PP 1 (vec A C))); intros.
replace (vec H H1) with (add_PP (vec H M) (vec M H1)).
Simplortho.
replace (vec M H1) with
 (add_PP (mult_PP 1 (vec M M1)) (mult_PP (-1) (vec H1 M1))).
Simplortho.
replace (vec M M1) with
 (add_PP (mult_PP (-1) (vec H M)) (mult_PP 1 (vec H M1))).
Simplortho.
rewrite <- (milieu_vecteur (A:=M) (B:=M1) (M:=H)); auto with geo.
Ringvec.
rewrite H22; auto with geo.
Ringvec.
Ringvec.
replace (vec A H1) with (add_PP (vec A C) (vec C H1)).
rewrite H19; rewrite H22; auto.
Ringvec.
Ringvec.
Ringvec.
Ringvec.
Ringvec.
unfold not in |- *; intros; apply H11.
cut (vec A B = vec C D); auto; intros.
rewrite H in H1.
apply conversion_PP with (a := 1) (b := 1); auto.
RingPP2 H1.
Ringvec.
discrR.
Qed.
 
Theorem composee_reflexions_axes_secants :
 forall (A B C M M' M1 : PO) (a : R),
 A <> B ->
 A <> C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 M1 = reflexion A B M -> M' = reflexion A C M1 -> M' = rotation A (a + a) M.
intros A B C M M' M1 a H H0 H1 H2 H3; try assumption.
elim (classic (A = M)).
intros H5; try assumption.
rewrite <- H5 in H2.
rewrite H2 in H3.
rewrite <- (reflexion_axe (A:=A) (B:=B) (M:=A)) in H3; auto with geo.
rewrite <- (reflexion_axe (A:=A) (B:=C) (M:=A)) in H3; auto with geo.
rewrite H3; rewrite <- H5.
apply rotation_def_centre.
elim (classic (alignes A B M)); intros.
cut (M1 = M); intros; auto.
rewrite H6 in H3.
elim (classic (alignes A C M)); intros.
cut (alignes A B C); intros.
cut (M' = M); intros.
rewrite H9.
pattern M at 1 in |- *.
rewrite (rotation_angle_nul A M).
apply deux_mes_angle_rotation.
symmetry  in |- *.
replace (image_angle (a + a)) with (double_AV (cons_AV (vec A B) (vec A C))).
apply angle_alignes; auto.
rewrite add_mes_compatible.
rewrite H1; auto.
rewrite H3; symmetry  in |- *.
apply reflexion_axe with (2 := H7); auto.
cut (alignes A M C); auto with geo; intros.
apply alignes_trans with M; auto with geo.
generalize (axe_reflexion_bissectrice (A:=A) (B:=C) (M:=M) (M':=M')); intros.
apply rotation_def2; auto.
generalize (reflexion_mediatrice (A:=A) (B:=C) (M:=M) (M':=M')); intros.
elim H9; intros; auto.
cut (cons_AV (vec A M) (vec A B) = cons_AV (vec A B) (vec A M)); intros.
replace (cons_AV (vec A M) (vec A M')) with
 (plus (plus (cons_AV (vec A M) (vec A B)) (cons_AV (vec A B) (vec A M1)))
    (plus (cons_AV (vec A M1) (vec A C)) (cons_AV (vec A C) (vec A M')))).
rewrite H6; rewrite H9; rewrite <- H8; auto.
replace
 (plus (plus (cons_AV (vec A B) (vec A M)) (cons_AV (vec A B) (vec A M)))
    (plus (cons_AV (vec A M) (vec A C)) (cons_AV (vec A M) (vec A C)))) with
 (plus (plus (cons_AV (vec A B) (vec A M)) (cons_AV (vec A M) (vec A C)))
    (plus (cons_AV (vec A B) (vec A M)) (cons_AV (vec A M) (vec A C)))).
replace (plus (cons_AV (vec A B) (vec A M)) (cons_AV (vec A M) (vec A C)))
 with (cons_AV (vec A B) (vec A C)).
rewrite <- H1; rewrite add_mes_compatible; auto.
rewrite Chasles; auto.
mesure A B A M.
mesure A M A C.
replace (x + x0 + (x + x0)) with (x + x + (x0 + x0)); auto.
ring.
rewrite H6.
rewrite Chasles; auto.
generalize (non_axe_image_non_axe (A:=A) (B:=C) (M:=M) (M':=M')); intros.
generalize (non_alignes_distincts (A:=A) (B:=C) (C:=M')); intros.
rewrite Chasles; auto.
rewrite Chasles; auto.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros; try clear existence_representant_unitaire | auto ].
elim existence_representant_unitaire with (A := A) (B := M);
 [ intros; try clear existence_representant_unitaire | auto ].
elim alignes_representant_unitaire with (A := A) (B := B) (C := M);
 [ intros; try clear alignes_representant_unitaire; auto
 | intros; auto
 | auto
 | auto
 | auto ].
rewrite H11; auto.
rewrite <- angles_representants_unitaires; auto.
rewrite <- angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
replace (representant_unitaire (vec A B)) with
 (mult_PP (-1) (representant_unitaire (vec A M))).
cut (A <> x0); intros.
replace (mult_PP (-1) (representant_unitaire (vec A M))) with (vec x0 A).
rewrite <- H10.
rewrite <- angle_plat; auto.
rewrite <- angle_plat; auto.
rewrite <- H10.
Ringvec.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := A) (B := M) (C := x0);
 [ intros; elim H13; intros H22 H23; rewrite H22; try discrR | auto | auto ].
rewrite H11; Ringvec.
rewrite H2.
rewrite <- reflexion_axe; auto.
generalize (non_axe_image_non_axe (A:=A) (B:=B) (M:=M) (M':=M1)); intros.
generalize (non_alignes_distincts (A:=A) (B:=B) (C:=M1)); intros.
elim (classic (alignes A C M1)); intros.
cut (M' = M1); intros; auto.
rewrite H9.
generalize (axe_reflexion_bissectrice (A:=A) (B:=B) (M:=M) (M':=M1)); intros.
apply rotation_def2; auto.
generalize (reflexion_mediatrice (A:=A) (B:=B) (M:=M) (M':=M1)); intros.
elim H11; intros; auto.
rewrite <- H9.
cut (cons_AV (vec A M') (vec A C) = cons_AV (vec A C) (vec A M')); intros.
replace (cons_AV (vec A M) (vec A M')) with
 (plus (plus (cons_AV (vec A M) (vec A B)) (cons_AV (vec A B) (vec A M1)))
    (plus (cons_AV (vec A M1) (vec A C)) (cons_AV (vec A C) (vec A M')))).
rewrite <- H11; rewrite H10; auto.
rewrite <- H9.
replace
 (plus (plus (cons_AV (vec A B) (vec A M')) (cons_AV (vec A B) (vec A M')))
    (plus (cons_AV (vec A M') (vec A C)) (cons_AV (vec A M') (vec A C))))
 with
 (plus (plus (cons_AV (vec A B) (vec A M')) (cons_AV (vec A M') (vec A C)))
    (plus (cons_AV (vec A B) (vec A M')) (cons_AV (vec A M') (vec A C)))).
replace (plus (cons_AV (vec A B) (vec A M')) (cons_AV (vec A M') (vec A C)))
 with (cons_AV (vec A B) (vec A C)).
rewrite <- H1; rewrite add_mes_compatible; auto.
rewrite H9; rewrite Chasles; auto.
rewrite H9.
mesure A B A M1.
mesure A M1 A C.
replace (x + x0 + (x + x0)) with (x + x + (x0 + x0)); auto.
ring.
rewrite H9; rewrite Chasles; auto.
rewrite Chasles; auto.
rewrite Chasles; auto.
rewrite H9.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros; try clear existence_representant_unitaire | auto ].
elim existence_representant_unitaire with (A := A) (B := M1);
 [ intros; try clear existence_representant_unitaire | auto ].
elim alignes_representant_unitaire with (A := A) (B := C) (C := M1);
 [ intros; try clear alignes_representant_unitaire; auto
 | intros; auto
 | auto
 | auto
 | auto ].
rewrite H13; auto.
replace (representant_unitaire (vec A C)) with
 (mult_PP (-1) (representant_unitaire (vec A M1))).
cut (A <> x0); intros.
replace (mult_PP (-1) (representant_unitaire (vec A M1))) with (vec x0 A).
rewrite <- H12.
replace (mult_PP (-1) (vec A x0)) with (vec x0 A).
rewrite <- angle_plat; auto.
rewrite <- angle_plat; auto.
Ringvec.
rewrite <- H12.
Ringvec.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := A) (B := M1) (C := x0);
 [ intros; elim H15; intros H22 H23; rewrite H22; try discrR | auto | auto ].
rewrite H13; Ringvec.
rewrite H3.
rewrite <- reflexion_axe; auto.
generalize (non_axe_image_non_axe (A:=A) (B:=C) (M:=M1) (M':=M')); intros.
generalize (non_alignes_distincts (A:=A) (B:=C) (C:=M')); intros.
generalize (axe_reflexion_bissectrice (A:=A) (B:=B) (M:=M) (M':=M1)); intros.
generalize (axe_reflexion_bissectrice (A:=A) (B:=C) (M:=M1) (M':=M')); intros.
apply rotation_def2; auto.
generalize (reflexion_mediatrice (A:=A) (B:=B) (M:=M) (M':=M1)); intros.
generalize (reflexion_mediatrice (A:=A) (B:=C) (M:=M1) (M':=M')); intros.
cut (distance A M = distance A M1); intros.
rewrite H15.
elim H13; intros; auto.
elim H14; intros; auto.
elim H13; intros; auto.
replace (cons_AV (vec A M) (vec A M')) with
 (plus (plus (cons_AV (vec A M) (vec A B)) (cons_AV (vec A B) (vec A M1)))
    (plus (cons_AV (vec A M1) (vec A C)) (cons_AV (vec A C) (vec A M')))).
rewrite <- H12; auto.
rewrite H11; auto.
replace
 (plus (plus (cons_AV (vec A B) (vec A M1)) (cons_AV (vec A B) (vec A M1)))
    (plus (cons_AV (vec A M1) (vec A C)) (cons_AV (vec A M1) (vec A C))))
 with
 (plus (plus (cons_AV (vec A B) (vec A M1)) (cons_AV (vec A M1) (vec A C)))
    (plus (cons_AV (vec A B) (vec A M1)) (cons_AV (vec A M1) (vec A C)))).
replace (plus (cons_AV (vec A B) (vec A M1)) (cons_AV (vec A M1) (vec A C)))
 with (cons_AV (vec A B) (vec A C)).
rewrite <- H1; rewrite add_mes_compatible; auto.
rewrite Chasles; auto.
mesure A B A M1.
mesure A M1 A C.
replace (x + x0 + (x + x0)) with (x + x + (x0 + x0)); auto.
ring.
rewrite Chasles; auto.
rewrite Chasles; auto.
rewrite Chasles; auto.
Qed.