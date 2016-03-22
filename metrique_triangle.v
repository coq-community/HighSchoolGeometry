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


Require Export euclidien_classiques.
Require Export trigo.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma produit_scalaire_Cosinus :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 scalaire (vec A B) (vec A C) =
 distance A B * (distance A C * Cos (cons_AV (vec A B) (vec A C))).
intros.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H2; try clear existence_representant_unitaire; try exact H2
 | auto ].
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros C' H3; try clear existence_representant_unitaire; try exact H3
 | auto ].
elim existence_ROND_AB with (A := A) (B := B'); [ intros D H10 | auto ].
elim H10; intros.
elim H4; intros H6 H7; try clear H4; try exact H7.
rewrite angles_representants_unitaires; auto with geo.
pattern (vec A B) at 1 in |- *.
rewrite distance_vecteur; auto.
pattern (vec A C) at 1 in |- *.
rewrite distance_vecteur; auto.
rewrite <- H3; rewrite <- H2.
pattern (vec A C') at 1 in |- *.
rewrite (coordonnees_Cos_Sin (O:=A) (I:=B') (J:=D) (M:=C')); auto.
replace
 (mult_PP (distance A C)
    (add_PP (mult_PP (Cos (cons_AV (vec A B') (vec A C'))) (vec A B'))
       (mult_PP (Sin (cons_AV (vec A B') (vec A C'))) (vec A D)))) with
 (add_PP
    (mult_PP (distance A C * Cos (cons_AV (vec A B') (vec A C'))) (vec A B'))
    (mult_PP (distance A C * Sin (cons_AV (vec A B') (vec A C'))) (vec A D))).
replace (mult_PP (distance A B) (vec A B')) with
 (add_PP (mult_PP (distance A B) (vec A B')) (mult_PP 0 (vec A D))).
Simplscal.
replace (scalaire (vec A B') (vec A D)) with 0.
rewrite H6; ring.
symmetry  in |- *; auto with geo.
Ringvec.
Ringvec.
elim def_representant_unitaire2 with (A := A) (B := C) (C := C');
 auto with geo; intros.
elim H5; auto with geo.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B'); auto;
 intros.
elim H4; auto with geo.
Qed.
 
Lemma produit_scalaire_cosinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 scalaire (vec A B) (vec A C) = distance A B * (distance A C * cos a).
intros.
rewrite produit_scalaire_Cosinus; auto.
rewrite (egalite_cos_Cos (A:=A) (B:=B) (C:=C) (x:=a)); auto.
Qed.
Hint Resolve carre_scalaire_distance: geo.
 
Lemma triangle_rectangle_Cos :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 orthogonal (vec B A) (vec B C) ->
 distance A B = distance A C * Cos (cons_AV (vec A B) (vec A C)).
intros.
cut
 (scalaire (vec A B) (vec A C) =
  distance A B * (distance A C * Cos (cons_AV (vec A B) (vec A C)))); 
 intros.
2: apply produit_scalaire_Cosinus; auto.
apply Rmult_eq_reg_l with (distance A B); auto with geo.
rewrite <- H2.
rewrite (scalaire_avec_projete (A:=A) (B:=B) (C:=C) (H:=B)); auto with geo.
Qed.
 
Lemma triangle_rectangle_cos :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance A B = distance A C * cos a.
intros.
rewrite (triangle_rectangle_Cos (A:=A) (B:=B) (C:=C)); auto.
rewrite (egalite_cos_Cos (A:=A) (B:=B) (C:=C) (x:=a)); auto.
Qed.
 
Lemma triangle_rectangle_absolu_cos :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance A B = distance A C * Rabs (cos a).
intros.
cut (/ distance A C >= 0); intros; auto with geo.
cut (distance A B >= 0); intros; auto with geo.
cut (cos a >= 0); intros.
rewrite Rabs_right; auto with real.
apply triangle_rectangle_cos; auto.
replace (cos a) with (distance A B * / distance A C).
RReplace 0 (0 * / distance A C).
apply Rmult_ge_compat_r; auto.
rewrite (triangle_rectangle_cos (A:=A) (B:=B) (C:=C) (a:=a)); intros;
 auto with geo.
field.
auto with geo.
apply Rinv_le_pos; auto with geo.
Qed.
 
Lemma orthogonal_distincts :
 forall A B C : PO,
 A <> B -> A <> C -> orthogonal (vec A B) (vec A C) -> B <> C.
intros.
apply non_alignes_distincts2 with A; auto.
apply orthogonal_non_alignes; auto with geo.
Qed.
 
Lemma triangle_rectangle_direct_sinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle pisurdeux = cons_AV (vec B C) (vec B A) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C B = distance C A * sin a.
intros.
cut (image_angle (pisurdeux + - a) = cons_AV (vec C A) (vec C B)); intros.
rewrite sin_cos_pisurdeux_moins_x.
rewrite <- cos_paire.
rewrite <-
 (triangle_rectangle_cos (A:=C) (B:=B) (C:=A) (a:=- (pisurdeux + - a)))
 ; auto with geo.
apply mes_oppx; auto.
replace (cons_AV (vec C A) (vec C B)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec A B) (vec A C)) (cons_AV (vec B C) (vec B A)))));
 auto with geo.
rewrite opp_plus_plus_opp; auto.
rewrite <- H3; rewrite <- H2.
repeat rewrite <- mes_opp.
repeat rewrite <- add_mes_compatible.
replace (pisurdeux + - a) with (pi + (- a + - pisurdeux)); auto.
unfold pi in |- *; ring.
Qed.
 
Lemma triangle_rectangle_indirect_sinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle (- pisurdeux) = cons_AV (vec B C) (vec B A) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C B = distance C A * - sin a.
intros A B C a H H0 H1 H2 H3; try assumption.
elim pisurdeux_plus_x with (x := a);
 [ intros H5 H6; try clear pisurdeux_plus_x; try rewrite <- H5 ].
rewrite <- (triangle_rectangle_cos (A:=C) (B:=B) (C:=A) (a:=pisurdeux + a));
 auto with geo.
cut (orthogonal (vec B A) (vec B C)); auto with geo.
apply pisurdeux_droit.
RReplace pisurdeux (- - pisurdeux).
apply mes_oppx; auto with geo.
RReplace (pisurdeux + a) (- - (pisurdeux + a)).
apply mes_oppx; auto with geo.
replace (cons_AV (vec C A) (vec C B)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec A B) (vec A C)) (cons_AV (vec B C) (vec B A)))));
 auto with geo.
rewrite opp_plus_plus_opp; auto.
rewrite <- H3; rewrite <- H2.
repeat rewrite <- mes_opp.
repeat rewrite <- add_mes_compatible.
rewrite <- (plus_angle_zero (image_angle (- (pisurdeux + a)))).
rewrite <- pi_plus_pi.
repeat rewrite <- add_mes_compatible.
replace (- (pisurdeux + a) + deuxpi) with (pi + (- a + - - pisurdeux)); auto.
unfold deuxpi, pi in |- *; ring.
Qed.
 
Lemma triangle_rectangle_absolu_sinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C B = distance C A * Rabs (sin a).
intros.
cut (/ distance C A >= 0); intros; auto with geo.
2: apply Rinv_le_pos; auto with geo.
cut (distance C B >= 0); intros; auto with geo.
elim orthogonal_pisurdeux_or with (A := B) (B := C) (C := B) (D := A);
 [ intros H10; try clear orthogonal_pisurdeux_or
 | intros H10; try clear orthogonal_pisurdeux_or
 | auto
 | auto
 | auto with geo ].
cut (sin a >= 0); intros.
rewrite Rabs_right; auto with real.
apply triangle_rectangle_direct_sinus; auto.
replace (sin a) with (distance C B * / distance C A).
RReplace 0 (0 * / distance C A).
apply Rmult_ge_compat_r; auto with geo.
rewrite (triangle_rectangle_direct_sinus (A:=A) (B:=B) (C:=C) (a:=a)); intros;
 auto with geo.
field.
auto with geo.
cut (- sin a >= 0); intros.
elim H6; clear H6; intros.
rewrite Rabs_left; auto with real.
apply triangle_rectangle_indirect_sinus; auto.
fourier.
rewrite Rabs_right; auto with real.
replace (sin a) with (- sin a).
apply triangle_rectangle_indirect_sinus; auto.
rewrite H6.
RReplace (sin a) (- - sin a).
rewrite H6; ring.
RReplace (sin a) (- - sin a).
rewrite H6; auto with real.
replace (- sin a) with (distance C B * / distance C A).
RReplace 0 (0 * / distance C A).
apply Rmult_ge_compat_r; auto.
rewrite (triangle_rectangle_indirect_sinus (A:=A) (B:=B) (C:=C) (a:=a));
 intros; auto with geo.
field.
auto with geo.
Qed.
 
Lemma triangle_rectangle_direct_Sin :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle pisurdeux = cons_AV (vec B C) (vec B A) ->
 distance C B = distance C A * Sin (cons_AV (vec A B) (vec A C)).
intros.
mes (cons_AV (vec A B) (vec A C)).
rewrite <- H3.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=x)); auto.
apply triangle_rectangle_direct_sinus; auto.
Qed.
 
Lemma triangle_rectangle_indirect_Sin :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle (- pisurdeux) = cons_AV (vec B C) (vec B A) ->
 distance C B = distance C A * - Sin (cons_AV (vec A B) (vec A C)).
intros.
mes (cons_AV (vec A B) (vec A C)).
rewrite <- H3.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=x)); auto.
apply triangle_rectangle_indirect_sinus; auto.
Qed.
 
Lemma triangle_rectangle_absolu_Sin :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 orthogonal (vec B A) (vec B C) ->
 distance C B = distance C A * Rabs (Sin (cons_AV (vec A B) (vec A C))).
intros.
mes (cons_AV (vec A B) (vec A C)).
rewrite <- H3.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=x)); auto.
apply triangle_rectangle_absolu_sinus; auto.
Qed.
 
Lemma projete_negatif_cos :
 forall (A B C H : PO) (a k : R),
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 vec A H = mult_PP k (vec A B) ->
 k < 0 -> image_angle a = cons_AV (vec A B) (vec A C) -> cos a < 0.
intros.
cut (scalaire (vec A B) (vec A C) < 0); intros.
replace (cos a) with
 (/ distance A B * / distance A C * scalaire (vec A B) (vec A C)).
RReplace 0 (/ distance A B * / distance A C * 0).
apply Rmult_lt_compat_l; auto with real.
apply Rmult_lt_0_compat; auto with real.
apply Rinv_0_lt_compat; auto with real.
cut (distance A B >= 0); intros; auto with geo.
elim H7; auto with real; intros.
absurd (distance A B = 0); auto with geo.
apply Rinv_0_lt_compat; auto with real.
cut (distance A C >= 0); intros; auto with geo.
elim H7; auto with real; intros.
absurd (distance A C = 0); auto with geo.
rewrite (produit_scalaire_cosinus (A:=A) (B:=B) (C:=C) (a:=a)); auto.
field; split; auto with geo.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := C) (H := H);
 [ intros; auto | auto | auto ].
rewrite (scalaire_avec_projete (A:=A) (B:=B) (C:=C) (H:=H)); auto with geo.
rewrite H3.
RReplace (scalaire (vec A B) (mult_PP k (vec A B)))
 (- (- k * scalaire (vec A B) (vec A B))).
apply Ropp_lt_gt_0_contravar; auto with real.
apply Rmult_gt_0_compat; auto with real.
cut (scalaire (vec A B) (vec A B) >= 0); intros; auto with geo.
elim H8; auto with real; intros.
absurd (scalaire (vec A B) (vec A B) = 0); auto with geo.
Simplscal.
Qed.
 
Lemma projete_absolu_cos :
 forall (A B C H : PO) (a : R),
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance A H = distance A C * Rabs (cos a).
intros.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := C) (H := H);
 [ intros; auto | auto | auto ].
halignes H4 ipattern:k.
cut (orthogonal (vec H A) (vec H C)); intros; auto with geo.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H8; try clear total_order
 | intros H8; elim H8;
    [ intros H9; try clear H8 | intros H9; try clear H8; try exact H9 ] ].
replace (Rabs (cos a)) with (Rabs (cos (a + pi))).
apply triangle_rectangle_absolu_cos; auto.
apply distinct_produit_vecteur with (3 := H6); auto with real.
rewrite H6; auto.
rewrite angle_produit_negatif_l; auto.
rewrite add_mes_compatible; rewrite <- H3; auto.
RReplace (a + pi) (pi + a).
elim pi_plus_x with (x := a);
 [ intros H9 H10; try clear pi_plus_x; rewrite H9 ].
rewrite Rabs_Ropp; auto.
cut (A = H); intros.
rewrite <- H8 in H5; auto.
elim droit_direct_ou_indirect with (A := A) (B := B) (C := C);
 [ intros H10; try clear droit_direct_ou_indirect
 | intros H10; try clear droit_direct_ou_indirect; try exact H10
 | auto
 | auto
 | auto ].
replace (cos a) with (cos pisurdeux).
rewrite cos_pisurdeux; rewrite Rabs_R0; ring_simplify.
rewrite <- H8; auto with geo.
apply cos_deux_mes.
rewrite H10; auto.
replace (cos a) with (cos (- pisurdeux)).
rewrite cos_paire; rewrite cos_pisurdeux; rewrite Rabs_R0; ring_simplify.
rewrite <- H8; auto with geo.
apply cos_deux_mes.
rewrite H10; auto.
apply produit_zero_conf with (1 := H6); auto.
apply triangle_rectangle_absolu_cos; auto.
apply distinct_produit_vecteur with (3 := H6); auto with real.
rewrite H6; auto.
rewrite angle_produit_positif_l; auto.
replace (vec H A) with (mult_PP (- k) (vec A B)).
Simplortho.
VReplace (vec H A) (mult_PP (-1) (vec A H)).
rewrite H6; Ringvec.
Qed.
 
Lemma projete_absolu_sin :
 forall (A B C H : PO) (a : R),
 triangle A B C ->
 H = projete_orthogonal A B C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C H = distance C A * Rabs (sin a).
intros.
deroule_triangle A B C.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := C) (H := H);
 [ intros; auto | auto | auto ].
halignes H7 ipattern:k.
cut (orthogonal (vec H A) (vec H C)); intros; auto with geo.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H11; try clear total_order
 | intros H11; elim H11;
    [ intros H12; try clear H11 total_order
    | intros H12; try clear H11 total_order; try exact H12 ] ].
replace (Rabs (sin a)) with (Rabs (sin (a + pi))).
apply triangle_rectangle_absolu_sinus; auto.
apply distinct_produit_vecteur with (3 := H9); auto with real.
red in |- *; intros; apply H3.
rewrite <- H12; auto with geo.
rewrite H9.
rewrite angle_produit_negatif_l; auto.
rewrite add_mes_compatible; rewrite <- H2; auto.
RReplace (a + pi) (pi + a).
elim pi_plus_x with (x := a);
 [ intros H12 H13; try clear pi_plus_x; rewrite H13 ].
rewrite Rabs_Ropp; auto.
cut (A = H); intros.
rewrite <- H13 in H8; auto.
elim droit_direct_ou_indirect with (A := A) (B := B) (C := C);
 [ intros H14; try clear droit_direct_ou_indirect
 | intros H14; try clear droit_direct_ou_indirect; try exact H14
 | auto
 | auto
 | auto ].
replace (sin a) with (sin pisurdeux).
rewrite sin_pisurdeux; rewrite Rabs_R1; ring_simplify.
rewrite <- H13; auto.
apply sin_deux_mes.
rewrite H14; auto.
replace (sin a) with (sin (- pisurdeux)).
rewrite sin_impaire; rewrite sin_pisurdeux.
rewrite Rabs_Ropp; rewrite Rabs_R1; ring_simplify.
rewrite <- H13; auto.
apply sin_deux_mes.
rewrite H14; auto.
apply produit_zero_conf with (1 := H9); auto.
apply triangle_rectangle_absolu_sinus; auto.
apply distinct_produit_vecteur with (3 := H9); auto with real.
red in |- *; intros; apply H3.
rewrite <- H13; auto with geo.
rewrite H9; auto.
rewrite angle_produit_positif_l; auto.
replace (vec H A) with (mult_PP (- k) (vec A B)).
Simplortho.
VReplace (vec H A) (mult_PP (-1) (vec A H)).
rewrite H9; Ringvec.
Qed.
 
Lemma projete_absolu_Sin :
 forall A B C H : PO,
 triangle A B C ->
 H = projete_orthogonal A B C ->
 distance C H = distance C A * Rabs (Sin (cons_AV (vec A B) (vec A C))).
intros.
deroule_triangle A B C.
mes (cons_AV (vec A B) (vec A C)).
rewrite <- H6.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=x)); auto.
apply projete_absolu_sin with B; auto.
Qed.
 
Lemma projete_absolu_Cos :
 forall A B C H : PO,
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 distance A H = distance A C * Rabs (Cos (cons_AV (vec A B) (vec A C))).
intros.
mes (cons_AV (vec A B) (vec A C)).
rewrite <- H3.
rewrite <- (egalite_cos_Cos (A:=A) (B:=B) (C:=C) (x:=x)); auto.
apply projete_absolu_cos with B; auto.
Qed.
 
Theorem Al_Kashi_Cos :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 Rsqr (distance B C) =
 Rsqr (distance A B) + Rsqr (distance A C) +
 - (2 * (distance A B * (distance A C * Cos (cons_AV (vec A B) (vec A C))))).
unfold Rsqr in |- *; intros.
repeat rewrite <- carre_scalaire_distance.
rewrite (difference_Pythagore A B C).
rewrite (produit_scalaire_Cosinus (A:=A) (B:=B) (C:=C)); auto.
ring.
Qed.
 
Theorem Al_Kashi :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 Rsqr (distance B C) =
 Rsqr (distance A B) + Rsqr (distance A C) +
 - (2 * (distance A B * (distance A C * cos a))).
unfold Rsqr in |- *; intros.
repeat rewrite <- carre_scalaire_distance.
rewrite (difference_Pythagore A B C).
rewrite (produit_scalaire_cosinus (A:=A) (B:=B) (C:=C) (a:=a)); auto.
ring.
Qed.
 
Lemma triangles_isometriques :
 forall (A B C A' B' C' : PO) (x x' y y' : R),
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B ->
 distance A' C' = distance A C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C') :>AV ->
 image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
 image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
 image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
 image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
 distance B' C' = distance B C /\ cos x = cos x' /\ cos y = cos y'.
intros.
mesure A B A C.
cut (A' <> B' /\ A' <> C'); intros.
elim H10; intros H22 H23; try clear H10.
cut (distance B' C' = distance B C); intros.
cut (B' <> C').
intros H21.
cut (2 <> 0).
intros H24.
split; [ try assumption | idtac ].
split; [ try assumption | idtac ].
cut
 (Rsqr (distance C A) =
  Rsqr (distance B C) + Rsqr (distance B A) +
  - (2 * (distance B C * (distance B A * cos x)))); 
 intros.
cut
 (Rsqr (distance C' A') =
  Rsqr (distance B' C') + Rsqr (distance B' A') +
  - (2 * (distance B' C' * (distance B' A' * cos x')))); 
 intros.
cut
 (2 * (distance B C * distance B A) * cos x =
  2 * (distance B' C' * distance B' A') * cos x'); 
 intros.
apply
 resolution2
  with
    (x := 2 * (distance B C * distance B A))
    (y := 2 * (distance B' C' * distance B' A')); auto with geo real.
rewrite (distance_sym B' A'); rewrite H10; rewrite H2;
 rewrite (distance_sym B A); ring.
replace (2 * (distance B' C' * distance B' A') * cos x') with
 (Rsqr (distance B' C') + Rsqr (distance B' A') + - Rsqr (distance C' A')).
replace (2 * (distance B C * distance B A) * cos x) with
 (Rsqr (distance B C) + Rsqr (distance B A) + - Rsqr (distance C A)).
rewrite (distance_sym B' A'); rewrite (distance_sym C' A'); rewrite H10;
 rewrite H2; rewrite H3; rewrite (distance_sym B A);
 rewrite (distance_sym C A); ring.
rewrite H11; ring.
rewrite H12; ring.
apply Al_Kashi; auto.
apply Al_Kashi; auto.
cut
 (Rsqr (distance A B) =
  Rsqr (distance C A) + Rsqr (distance C B) +
  - (2 * (distance C A * (distance C B * cos y)))); 
 intros.
cut
 (Rsqr (distance A' B') =
  Rsqr (distance C' A') + Rsqr (distance C' B') +
  - (2 * (distance C' A' * (distance C' B' * cos y')))); 
 intros.
cut
 (2 * (distance C A * distance C B) * cos y =
  2 * (distance C' A' * distance C' B') * cos y'); 
 intros.
apply
 resolution2
  with
    (x := 2 * (distance C A * distance C B))
    (y := 2 * (distance C' A' * distance C' B')); auto with geo real.
rewrite (distance_sym C' A'); rewrite H3; rewrite (distance_sym C' B');
 rewrite H10; rewrite (distance_sym C B); rewrite (distance_sym C A); 
 ring.
replace (2 * (distance C A * distance C B) * cos y) with
 (Rsqr (distance C A) + Rsqr (distance C B) + - Rsqr (distance A B)).
replace (2 * (distance C' A' * distance C' B') * cos y') with
 (Rsqr (distance C' A') + Rsqr (distance C' B') + - Rsqr (distance A' B')).
rewrite (distance_sym C' B'); rewrite (distance_sym C' A'); rewrite H10;
 rewrite H2; rewrite H3; rewrite (distance_sym C B);
 rewrite (distance_sym C A); ring.
rewrite H12; ring.
rewrite H11; ring.
apply Al_Kashi; auto.
apply Al_Kashi; auto.
discrR.
apply dist_non_nulle; rewrite H10; auto with geo.
apply distance_carre; auto.
mesure A B A C.
rewrite (Al_Kashi (A:=A') (B:=B') (C:=C') (a:=x0)); auto.
rewrite (Al_Kashi (A:=A) (B:=B) (C:=C) (a:=x0)); auto.
rewrite H2; rewrite H3; ring.
rewrite H9; rewrite H4; auto.
split; [ idtac | try assumption ].
apply dist_non_nulle; rewrite H2; auto with geo.
apply dist_non_nulle; rewrite H3; auto with geo.
Qed.
 
Axiom
  angles_egaux_triangle :
    forall (A B C A' B' C' : PO) (x x' y y' : R),
    A <> B :>PO ->
    A <> C :>PO ->
    B <> C :>PO ->
    cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C') :>AV ->
    image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
    image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
    image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
    image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
    cos x = cos x' ->
    cos y = cos y' ->
    cons_AV (vec B C) (vec B A) = cons_AV (vec B' C') (vec B' A') :>AV /\
    cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
 
Lemma cas_egalite_triangle :
 forall A B C A' B' C' : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B ->
 distance A' C' = distance A C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C') :>AV ->
 distance B' C' = distance B C /\
 cons_AV (vec B C) (vec B A) = cons_AV (vec B' C') (vec B' A') :>AV /\
 cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
intros.
cut (A' <> B' /\ A' <> C'); intros.
elim H5; intros H6 H7; try clear H5; try exact H7.
mesure A B A C.
cut (distance B' C' = distance B C).
intros H20.
cut (B' <> C').
intros H21.
mesure B C B A.
mesure B' C' B' A'.
mesure C A C B.
mesure C' A' C' B'.
rewrite H11; rewrite H10; rewrite H9; rewrite H8.
elim
 triangles_isometriques
  with
    (A := A)
    (B := B)
    (C := C)
    (A' := A')
    (B' := B')
    (C' := C')
    (x := x0)
    (x' := x1)
    (y := x2)
    (y' := x3);
 [ intros; try exact H0
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto ].
split; [ try assumption | idtac ].
elim H13; intros H14 H15; try clear H13; try exact H15.
apply angles_egaux_triangle with (9 := H14) (10 := H15); auto.
apply dist_non_nulle; rewrite H20; auto with geo.
cut (Rsqr (distance B' C') = Rsqr (distance B C)); intros.
apply resolution; auto with geo real.
rewrite (Al_Kashi (A:=A') (B:=B') (C:=C') (a:=x)); auto.
rewrite (Al_Kashi (A:=A) (B:=B) (C:=C) (a:=x)); auto.
rewrite H2; rewrite H3; ring.
rewrite H5; rewrite H4; auto.
split; [ idtac | try assumption ].
apply dist_non_nulle; rewrite H2; auto with geo.
apply dist_non_nulle; rewrite H3; auto with geo.
Qed.
 
Lemma triangles_isometriques_indirects :
 forall (A B C A' B' C' : PO) (x x' y y' : R),
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B ->
 distance A' C' = distance A C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' C') (vec A' B') :>AV ->
 image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
 image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
 image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
 image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
 distance B' C' = distance B C /\ cos x = cos x' /\ cos y = cos y'.
intros.
mesure A B A C.
cut (A' <> B' /\ A' <> C'); intros.
elim H10; intros H22 H23; try clear H10.
cut (distance B' C' = distance B C); intros.
cut (B' <> C').
intros H21.
cut (2 <> 0).
intros H24.
split; [ try assumption | idtac ].
split; [ try assumption | idtac ].
cut
 (Rsqr (distance C A) =
  Rsqr (distance B C) + Rsqr (distance B A) +
  - (2 * (distance B C * (distance B A * cos x)))); 
 intros.
cut
 (Rsqr (distance C' A') =
  Rsqr (distance B' C') + Rsqr (distance B' A') +
  - (2 * (distance B' C' * (distance B' A' * cos x')))); 
 intros.
cut
 (2 * (distance B C * distance B A) * cos x =
  2 * (distance B' C' * distance B' A') * cos x'); 
 intros.
apply
 resolution2
  with
    (x := 2 * (distance B C * distance B A))
    (y := 2 * (distance B' C' * distance B' A')); auto with geo real.
rewrite (distance_sym B' A'); rewrite H10; rewrite H2;
 rewrite (distance_sym B A); ring.
replace (2 * (distance B' C' * distance B' A') * cos x') with
 (Rsqr (distance B' C') + Rsqr (distance B' A') + - Rsqr (distance C' A')).
replace (2 * (distance B C * distance B A) * cos x) with
 (Rsqr (distance B C) + Rsqr (distance B A) + - Rsqr (distance C A)).
rewrite (distance_sym B' A'); rewrite (distance_sym C' A'); rewrite H10;
 rewrite H2; rewrite H3; rewrite (distance_sym B A);
 rewrite (distance_sym C A); ring.
rewrite H11; ring.
rewrite H12; ring.
apply Al_Kashi; auto.
apply Al_Kashi; auto.
cut
 (Rsqr (distance A B) =
  Rsqr (distance C A) + Rsqr (distance C B) +
  - (2 * (distance C A * (distance C B * cos y)))); 
 intros.
cut
 (Rsqr (distance A' B') =
  Rsqr (distance C' A') + Rsqr (distance C' B') +
  - (2 * (distance C' A' * (distance C' B' * cos y')))); 
 intros.
cut
 (2 * (distance C A * distance C B) * cos y =
  2 * (distance C' A' * distance C' B') * cos y'); 
 intros.
apply
 resolution2
  with
    (x := 2 * (distance C A * distance C B))
    (y := 2 * (distance C' A' * distance C' B')); auto with geo real.
rewrite (distance_sym C' A'); rewrite H3; rewrite (distance_sym C' B');
 rewrite H10; rewrite (distance_sym C B); rewrite (distance_sym C A); 
 ring.
replace (2 * (distance C A * distance C B) * cos y) with
 (Rsqr (distance C A) + Rsqr (distance C B) + - Rsqr (distance A B)).
replace (2 * (distance C' A' * distance C' B') * cos y') with
 (Rsqr (distance C' A') + Rsqr (distance C' B') + - Rsqr (distance A' B')).
rewrite (distance_sym C' B'); rewrite (distance_sym C' A'); rewrite H10;
 rewrite H2; rewrite H3; rewrite (distance_sym C B);
 rewrite (distance_sym C A); ring.
rewrite H12; ring.
rewrite H11; ring.
apply Al_Kashi; auto.
apply Al_Kashi; auto.
discrR.
apply dist_non_nulle; rewrite H10; auto with geo.
apply distance_carre.
mesure A B A C.
rewrite (Al_Kashi (A:=A) (B:=B) (C:=C) (a:=x1)); auto.
rewrite (Al_Kashi (A:=A') (B:=B') (C:=C') (a:=- x1)); auto.
rewrite H2; rewrite H3; rewrite cos_paire; ring.
apply (mes_oppx (A:=A') (B:=C') (C:=A') (D:=B') (x:=x1)); auto.
rewrite H10; rewrite H4; auto.
split; [ idtac | try assumption ].
apply dist_non_nulle; rewrite H2; auto with geo.
apply dist_non_nulle; rewrite H3; auto with geo.
Qed.
 
Axiom
  angles_egaux_triangle_indirect :
    forall (A B C A' B' C' : PO) (x x' y y' : R),
    A <> B :>PO ->
    A <> C :>PO ->
    B <> C :>PO ->
    cons_AV (vec A B) (vec A C) = cons_AV (vec A' C') (vec A' B') :>AV ->
    image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
    image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
    image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
    image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
    cos x = cos x' :>R ->
    cos y = cos y' :>R ->
    cons_AV (vec B C) (vec B A) = cons_AV (vec B' A') (vec B' C') :>AV /\
    cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
 
Lemma cas_egalite_triangle_indirect :
 forall A B C A' B' C' : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B :>R ->
 distance A' C' = distance A C :>R ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' C') (vec A' B') :>AV ->
 distance B' C' = distance B C :>R /\
 cons_AV (vec B C) (vec B A) = cons_AV (vec B' A') (vec B' C') :>AV /\
 cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
intros.
cut (A' <> B' /\ A' <> C'); intros.
elim H5; intros H6 H7; try clear H5; try exact H7.
mesure A B A C.
cut (distance B' C' = distance B C).
intros H20.
cut (B' <> C').
intros H21.
mesure B C B A.
mesure B' C' B' A'.
mesure C A C B.
mesure C' A' C' B'.
rewrite H8; rewrite H10; rewrite H11.
elim
 triangles_isometriques_indirects
  with
    (A := A)
    (B := B)
    (C := C)
    (A' := A')
    (B' := B')
    (C' := C')
    (x := x0)
    (x' := x1)
    (y := x2)
    (y' := x3);
 [ intros; try exact H0
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto ].
split; [ try assumption | idtac ].
elim H13; intros H14 H15; try clear H13; try exact H15.
apply
 angles_egaux_triangle_indirect
  with (x := x0) (x' := x1) (y := x2) (y' := x3); auto.
apply dist_non_nulle; rewrite H20; auto with geo.
apply distance_carre.
rewrite (Al_Kashi (A:=A) (B:=B) (C:=C) (a:=x)); auto.
rewrite (Al_Kashi (A:=A') (B:=B') (C:=C') (a:=- x)); auto.
rewrite H2; rewrite H3; rewrite cos_paire; ring.
apply (mes_oppx (A:=A') (B:=C') (C:=A') (D:=B') (x:=x)); auto.
rewrite H5; rewrite H4; auto.
split; [ idtac | try assumption ].
apply dist_non_nulle; rewrite H2; auto with geo.
apply dist_non_nulle; rewrite H3; auto with geo.
Qed.
