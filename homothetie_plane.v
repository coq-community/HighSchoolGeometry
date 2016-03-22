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


Require Export dilatations.
Require Export affine_classiques.
Require Export cercle.
Require Export rotation_plane.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma homothetie_conserve_angle :
 forall (I A B C A' B' C' : PO) (k : R),
 k <> 0 ->
 A <> B ->
 A <> C ->
 A' = homothetie k I A ->
 B' = homothetie k I B ->
 C' = homothetie k I C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C').
intros.
cut (vec A' B' = mult_PP k (vec A B)); intros.
cut (vec A' C' = mult_PP k (vec A C)); intros.
cut (A' <> B'); intros.
cut (A' <> C'); intros.
rewrite H5.
elim Rtotal_order with (r1 := k) (r2 := 0); intros.
rewrite angle_produit_negatif_l; auto.
rewrite H6.
rewrite angle_produit_negatif_r2; auto.
rewrite <- plus_associative.
rewrite <- add_mes_compatible.
replace (pi + pi) with deuxpi; auto.
rewrite pi_plus_pi.
rewrite plus_angle_zero; auto.
elim H9;
 [ intros H10; try clear H9 | intros H10; try clear H9; try exact H10 ].
absurd (k = 0); auto with real.
rewrite angle_produit_positif_l; auto.
rewrite H6.
rewrite angle_produit_positif_r2; auto.
apply image_homothetie_distincts with (3 := H2) (4 := H4); auto.
apply image_homothetie_distincts with (3 := H2) (4 := H3); auto.
apply homothetie_bipoint with I; auto.
apply homothetie_bipoint with I; auto.
Qed.
 
Lemma distance_homothetie :
 forall (k : R) (I A A' B B' : PO),
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B :>PO -> distance A' B' = Rabs k * distance A B.
unfold distance in |- *; intros.
rewrite <- sqrt_Rsqr_abs.
rewrite <- sqrt_mult; intros.
apply Rsqr_inj; auto with real geo.
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=A) (B:=B) (A':=A') (B':=B'));
 intros.
replace (Rsqr k * scalaire (vec A B) (vec A B)) with
 (scalaire (mult_PP k (vec A B)) (mult_PP k (vec A B))).
rewrite H1; auto.
unfold Rsqr; Simplscal.
auto with real.
generalize scalaire_positif; intros; auto with real.
Qed.
 
Lemma intersection_homothetie :
 forall (k : R) (I A A' B B' C C' D D' K K' : PO),
 k <> 0 :>R ->
 A <> B ->
 C <> D ->
 ~ alignes A B C \/ ~ alignes A B D ->
 K = pt_intersection (droite A B) (droite C D) :>PO ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B ->
 C' = homothetie k I C :>PO ->
 D' = homothetie k I D :>PO ->
 K' = pt_intersection (droite A' B') (droite C' D') :>PO ->
 K' = homothetie k I K :>PO.
intros.
elim existence_homothetique with (k := k) (I := I) (A := K); intros L H13.
rewrite <- H13; rewrite H8; symmetry  in |- *.
apply
 (homothetie_intersection (k:=k) (I:=I) (A:=A) (A':=A') (B:=B) (B':=B')
    (C:=C) (C':=C') (D:=D) (D':=D') (K:=K) (K':=L)); 
 auto.
Qed.
 
Theorem paralleles_homothetie :
 forall A B C I J : PO,
 triangle A B C ->
 I <> J :>PO ->
 alignes A B I ->
 paralleles (droite B C) (droite I J) ->
 alignes A C J ->
 exists k : R, I = homothetie k A B :>PO /\ J = homothetie k A C :>PO.
intros.
deroule_triangle A B C.
halignes H1 ipattern:x.
cut (triangle B C A); intros; auto with geo.
elim (classic (x = 0)); intros.
cut (A = I); intros.
absurd (paralleles (droite I J) (droite B C)); auto with geo.
rewrite (droite_permute (A:=I) (B:=J)); auto.
apply concours_non_paralleles; auto.
rewrite <- H11; auto.
apply def_concours with C; auto with geo.
rewrite <- H11; auto.
apply alignes_ordre_cycle; auto with geo.
apply vecteur_nul_conf.
rewrite H8; rewrite H10; Ringvec.
exists x; split; apply vecteur_homothetie; auto.
generalize (Thales_concours (k:=x) (A:=A) (B:=B) (C:=C) (I:=I)); intros H18;
 apply H18; auto.
Qed.
 
Lemma centre_gravite_homothetie :
 forall A B C I G : PO,
 I = milieu B C :>PO ->
 G = centre_gravite A B C :>PO -> I = homothetie (- / 2) G A :>PO.
intros.
apply vecteur_homothetie.
replace (vec G A) with (mult_PP (-1) (vec A G)).
replace (vec G I) with (add_PP (vec A I) (mult_PP (-1) (vec A G))).
rewrite (centre_gravite_mediane_vecteur (A:=A) (B:=B) (C:=C) (I:=I) (G:=G));
 auto.
cut (3 <> 0); intros; auto with real.
cut (2 <> 0); intros; auto with real.
apply mult_PP_regulier with 2; auto.
replace
 (mult_PP 2
    (mult_PP (- / 2) (mult_PP (-1) (mult_PP (/ 3) (mult_PP 2 (vec A I))))))
 with (mult_PP (2 * / 2) (mult_PP (/ 3 * 2) (vec A I))).
replace (2 * / 2) with 1; auto with real.
Fieldvec 3.
repeat rewrite mult_mult_vec.
replace (2 * / 2 * (/ 3 * 2)) with (2 * (- / 2 * (-1 * (/ 3 * 2)))); auto.
field.
discrR.
Ringvec.
Ringvec.
Qed.
 
Lemma homothetie_mediatrice_hauteur :
 forall A B C I G J H : PO,
 triangle A B C ->
 I <> J ->
 I = milieu B C :>PO ->
 mediatrice B C J ->
 G = centre_gravite A B C :>PO ->
 H = homothetie (-2) G J :>PO -> orthogonal (vec A H) (vec B C).
intros.
deroule_triangle A B C.
cut (-2 <> 0); intros.
cut (A = homothetie (-2) G I); intros.
cut (A <> H); intros.
cut (paralleles (droite I J) (droite A H)); intros.
apply paralleles_orthogonal with (3 := H13); auto.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
apply paralleles_sym; auto.
apply homothetie_droite with (3 := H11) (4 := H5); auto.
apply image_homothetie_distincts with (3 := H11) (4 := H5); auto.
replace (-2) with (/ - / 2).
apply homothetie_inverse; auto with real.
apply centre_gravite_homothetie with (2 := H4); auto.
rewrite Ropp_inv_permute; auto with real.
discrR.
Qed.
 
Lemma homothetie_cercle :
 forall (k : R) (I A A' O O' M M' : PO),
 k <> 0 :>R ->
 O' = homothetie k I O :>PO ->
 A' = homothetie k I A :>PO ->
 M' = homothetie k I M :>PO ->
 cercle O (distance O A) M -> cercle O' (distance O' A') M'.
unfold cercle in |- *; intros.
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=O) (B:=M) (A':=O') (B':=M'));
 intros H5.
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=O) (B:=A) (A':=O') (B':=A'));
 intros.
apply carre_scalaire_egalite_distance.
rewrite H5; auto.
rewrite H4; auto.
Simplscal.
repeat rewrite carre_scalaire_distance; auto.
rewrite H3; ring.
Qed.
 
Lemma symetrie_rotation :
 forall A B I : PO, B = symetrie I A :>PO -> B = rotation I pi A :>PO.
intros.
generalize symetrie_milieu; intros.
discrimine I A.
rewrite <- rotation_def_centre.
rewrite H; rewrite H1.
symmetry  in |- *.
apply milieu_symetrie; auto with geo.
apply rotation_def2; auto with geo.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=I)).
apply angle_plat; auto.
apply H0; auto.
Qed.
 
Lemma rotation_symetrie :
 forall A B I : PO, B = rotation I pi A :>PO -> B = symetrie I A :>PO.
intros.
apply milieu_symetrie; auto.
discrimine I A.
rewrite H; rewrite <- H0; rewrite <- rotation_def_centre; auto with geo.
elim rotation_def with (I := I) (A := A) (B := B) (a := pi);
 [ try clear rotation_def; intros | auto | auto ].
cut (A <> B); intros.
apply alignes_mediatrice_milieu; auto.
cut (alignes I A B); intros; [ auto with geo | idtac ].
apply alignes_angle; auto with geo.
apply image_distinct_centre with (2 := H); auto.
unfold double_AV in |- *.
rewrite <- H2; rewrite <- pi_plus_pi; auto.
rewrite <- add_mes_compatible; auto.
red in |- *; intros; apply H0.
cut (Rsqr (distance A B) = (2 + 2) * Rsqr (distance I A)); intros.
apply distance_nulle; auto.
rewrite carre_scalaire_distance.
replace (distance I A * distance I A) with
 (/ (2 + 2) * (distance A B * distance A B)).
rewrite <- carre_scalaire_distance.
apply Rmult_eq_0_compat.
right; try assumption.
rewrite H3.
replace (vec B B) with (mult_PP 0 (vec B B)); [ idtac | Ringvec ].
Simplscal.
replace (distance A B * distance A B) with (Rsqr (distance A B));
 auto with real.
rewrite H4.
cut (2 + 2 <> 0); intros.
replace (/ (2 + 2) * ((2 + 2) * Rsqr (distance I A))) with
 (/ (2 + 2) * (2 + 2) * Rsqr (distance I A)); [ idtac | ring ].
replace (/ (2 + 2) * (2 + 2)) with 1; auto with real.
discrR.
rewrite (Al_Kashi (A:=I) (B:=A) (C:=B) (a:=pi)); auto.
rewrite cos_pi; auto.
rewrite <- H1.
unfold Rsqr; ring.
apply image_distinct_centre with (2 := H); auto.
Qed.
