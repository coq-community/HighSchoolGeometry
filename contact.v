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


Require Export complements_cercle.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma existence_intersection_droite_cercle_centre :
 forall (r : R) (A B : PO),
 A <> B -> r >= 0 -> exists C : PO, alignes A B C /\ distance A C = r.
intros.
assert (distance A B <> 0); auto with geo.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := B) (k := / distance A B * r); 
 intros C H2.
exists C.
split; [ try assumption | idtac ].
apply (colineaire_alignes H2); auto.
assert (Rsqr (distance A C) = Rsqr r).
unfold Rsqr in |- *; repeat rewrite <- carre_scalaire_distance.
rewrite H2.
Simplscal.
rewrite carre_scalaire_distance.
field.
auto with real.
auto with real.
apply Rsqr_inj; auto with geo real.
Qed.
 
Theorem intersection_cercle_droite :
 forall A B O D H : PO,
 A <> B ->
 H = projete_orthogonal A B O ->
 distance O H <= distance O D ->
 exists C : PO, alignes A B C /\ cercle_rayon O D C.
icercle.
assert (Rsqr (distance O D) + - Rsqr (distance O H) >= 0).
unfold Rsqr in |- *.
RReplace (distance O D * distance O D + - (distance O H * distance O H))
 ((distance O D + - distance O H) * (distance O D + distance O H)).
assert (distance O D >= 0); auto with geo.
assert (distance O H >= 0); auto with geo.
assert (distance O D + distance O H >= 0).
fourier.
assert (distance O D + - distance O H >= 0).
fourier.
RReplace 0 (0 * (distance O D + distance O H)).
apply Rmult_ge_compat_r; auto.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := O) (H := H);
 [ intros; auto | auto | auto ].
discrimine H A.
assert (H <> B).
contrapose H0.
rewrite <- H7; auto.
elim
 existence_intersection_droite_cercle_centre
  with
    (r := sqrt (Rsqr (distance O D) + - Rsqr (distance O H)))
    (A := H)
    (B := B);
 [ intros C H8; elim H8; [ intros H9 H10; try clear H8; try exact H10 ]
 | auto
 | auto ].
exists C; split; auto.
assert (Rsqr (distance O D) = Rsqr (distance O C)).
elim (Pythagore H O C); intros.
rewrite H8; auto.
replace (Rsqr (distance H C)) with (distance H C * distance H C);
 auto with real.
rewrite H10.
rewrite sqrt_sqrt; auto with real.
rewrite (distance_sym H O); ring.
halignes H9 ipattern:k.
apply ortho_sym.
rewrite H12; pattern H at 1 in |- *; rewrite H6; auto with geo.
auto with real.
apply Rsqr_inj; auto with geo real.
auto with real.
elim
 existence_intersection_droite_cercle_centre
  with
    (r := sqrt (Rsqr (distance O D) + - Rsqr (distance O H)))
    (A := H)
    (B := A);
 [ intros C H8; elim H8; [ intros H9 H10; try clear H8; try exact H10 ]
 | auto
 | auto ].
exists C; split; auto.
halignes H9 ipattern:k.
halignes H4 ipattern:k'.
apply colineaire_alignes with (k' + - (k * k')).
VReplace (vec A C) (add_PP (vec A H) (vec H C)).
rewrite H7.
VReplace (vec H A) (mult_PP (-1) (vec A H)).
rewrite H8; Ringvec.
assert (Rsqr (distance O D) = Rsqr (distance O C)).
elim (Pythagore H O C); intros.
rewrite H7; auto.
replace (Rsqr (distance H C)) with (distance H C * distance H C);
 auto with real.
rewrite H10.
rewrite sqrt_sqrt; auto with real.
rewrite (distance_sym H O); ring.
halignes H9 ipattern:k.
halignes H4 ipattern:k'.
apply ortho_sym.
rewrite H11.
VReplace (vec H A) (mult_PP (-1) (vec A H)).
rewrite H12.
VReplace (mult_PP k (mult_PP (-1) (mult_PP k' (vec A B))))
 (mult_PP (- (k * k')) (vec A B)).
auto with geo.
apply Rsqr_inj; auto with geo real.
auto with real.
Qed.
 
Lemma unicite_contact_cercle_droite_tangente :
 forall A B O D H C : PO,
 A <> B ->
 H = projete_orthogonal A B O ->
 cercle_rayon O D H -> alignes A B C -> cercle_rayon O D C -> H = C.
icercle.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := O) (H := H);
 [ intros; auto | auto | auto ].
elim (Pythagore H O C); intros.
assert (distance H C = 0); auto with geo.
apply Rsqr_inj; auto with geo real.
assert (Rsqr (distance O C) + - Rsqr (distance H O) = 0).
rewrite (distance_sym H O).
rewrite <- H4; rewrite <- H2; (unfold Rsqr in |- *; ring).
replace (Rsqr 0) with 0; [ idtac | unfold Rsqr in |- *; ring ].
rewrite <- H9; rewrite H7; auto.
unfold Rsqr in |- *; ring.
halignes H3 ipattern:x.
halignes H5 ipattern:y.
apply ortho_sym.
replace (vec H C) with (mult_PP (x + - y) (vec A B)); auto with geo.
VReplace (vec H C) (add_PP (vec A C) (mult_PP (-1) (vec A H))).
rewrite H11; rewrite H10; Ringvec.
Qed.
 
Theorem tangente_cercle_contact_unique :
 forall A B O M C : PO,
 B <> M ->
 tangente_cercle O A B M -> alignes B M C -> cercle_rayon O A C -> B = C.
intros.
hcercle H0.
assert (B = projete_orthogonal B M O).
apply def_projete_orthogonal; auto with geo.
apply
 (unicite_contact_cercle_droite_tangente (A:=B) (B:=M) (O:=O) (D:=A) (H:=B)
    (C:=C)); auto.
Qed.
 
Theorem intersection2_cercle_droite :
 forall A B O H : PO,
 A <> B ->
 O <> A ->
 H = projete_orthogonal A B O ->
 distance O H < distance O A ->
 exists C : PO, A <> C /\ alignes A B C /\ cercle_rayon O A C.
icercle.
assert (Rsqr (distance O A) + - Rsqr (distance O H) > 0).
unfold Rsqr in |- *.
assert (distance O A <> 0); auto with geo.
cut (distance O A >= 0); auto with geo.
unfold Rge in |- *; intros.
elim H5;
 [ intros H6; try clear H5 | intros H6; absurd (distance O A = 0); auto ].
RReplace (distance O A * distance O A + - (distance O H * distance O H))
 ((distance O A + - distance O H) * (distance O A + distance O H)).
assert (0 < distance O A + - distance O H).
fourier.
assert (0 < distance O A + distance O H).
apply Rplus_lt_le_0_compat; auto with real geo.
assert (0 < (distance O A + - distance O H) * (distance O A + distance O H)).
apply Rmult_lt_0_compat; auto with real.
fourier.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := O) (H := H);
 [ intros; auto | auto | auto ].
assert (H <> A).
assert (distance O H <> distance O A); auto with real.
contrapose H7.
rewrite <- H8; auto.
halignes H5 ipattern:k.
elim existence_symetrique with (A := H) (B := A); (intros C; intros).
assert (H = milieu A C); auto with geo.
assert (vec A C = mult_PP 2 (vec A H)); auto with geo.
exists C; split; auto.
generalize (distinct_produit_vecteur (A:=A) (B:=H) (C:=C) (a:=2)); intros H18;
 apply H18; auto with real geo.
split; [ idtac | try assumption ].
apply colineaire_alignes with (2 * k).
rewrite H11; rewrite H8; Ringvec.
assert (Rsqr (distance O A) = Rsqr (distance O C)).
elim (Pythagore H O C); intros.
rewrite H12; auto.
replace (Rsqr (distance H C)) with (Rsqr (distance H A)).
elim (Pythagore H O A); intros.
rewrite H14; auto.
apply ortho_sym.
replace (vec H A) with (mult_PP (- k) (vec A B)).
auto with geo.
VReplace (vec H A) (mult_PP (-1) (vec A H)).
rewrite H8; Ringvec.
rewrite (milieu_distance H10); auto.
replace (vec H C) with (vec A H).
apply ortho_sym.
rewrite H8; auto with geo.
auto with geo.
auto with geo.
Qed.
 
Definition cercles_tangents (O A O' A' : PO) :=
  O <> A ->
  O' <> A' ->
  exists B : PO, alignes O B O' /\ cercle_rayon O A B /\ cercle_rayon O' A' B.
 
Lemma auto_cercles_tangents :
 forall O A : PO, O <> A -> cercles_tangents O A O A.
unfold cercles_tangents in |- *; intros.
exists A.
icercle.
Qed.
 
Lemma cercles_concentriques_tangents_egaux :
 forall O A A' : PO,
 O <> A -> O <> A' -> cercles_tangents O A O A' -> cercle_rayon O A A'.
unfold cercles_tangents in |- *; icercle.
elim H1;
 [ intros B H2; elim H2;
    [ intros H3 H4; elim H4;
       [ intros H5 H6; try clear H4 H2 H1; try exact H5 ] ]
 | auto
 | auto ].
rewrite H6; auto.
Qed.
 
Lemma cercles_tangents_tangente_commune :
 forall O A O' A' : PO,
 O <> A ->
 O' <> A' ->
 cercles_tangents O A O' A' ->
 exists B : PO,
   (exists M : PO,
      B <> M /\ tangente_cercle O A B M /\ tangente_cercle O' A' B M).
unfold cercles_tangents, tangente_cercle in |- *; intros.
elim H1;
 [ intros B H2; elim H2;
    [ intros H3 H4; elim H4;
       [ intros H5 H6; try clear H4 H2 H1; try exact H5 ] ]
 | auto
 | auto ].
assert (O <> B).
hcercle H5.
apply (isometrie_distinct (A:=O) (B:=A) (A':=O) (B':=B)); auto with geo.
soit_orthogonal B O ipattern:M.
exists B; exists M.
split;
 [ auto
 | split; [ split; [ try assumption | auto with geo ] | try assumption ] ].
split; [ try assumption | idtac ].
halignes H3 ipattern:k.
apply ortho_sym.
VReplace (vec B O') (add_PP (vec B O) (vec O O')).
rewrite H7.
VReplace (add_PP (vec B O) (mult_PP k (vec O B)))
 (mult_PP (- k + 1) (vec B O)).
auto with geo.
Qed.
 
Lemma tangente_commune_cercles_tangents :
 forall O A O' A' B M : PO,
 O <> A ->
 O' <> A' ->
 B <> M ->
 tangente_cercle O A B M ->
 tangente_cercle O' A' B M -> cercles_tangents O A O' A'.
unfold cercles_tangents, tangente_cercle in |- *; intros.
repeat applatit_and.
exists B.
split; [ idtac | split; try assumption ].
assert (O <> B).
hcercle H3.
apply (isometrie_distinct (A:=O) (B:=A) (A':=O) (B':=B)); auto with geo.
elim
 orthogonal_colineaires
  with (A := B) (B := M) (C := B) (D := O) (E := B) (F := O');
 [ intros | auto | auto | auto | auto ].
apply colineaire_alignes with (- x + 1).
VReplace (vec O O') (add_PP (vec O B) (vec B O')).
rewrite H9.
VReplace (add_PP (vec O B) (mult_PP x (vec B O)))
 (mult_PP (- x + 1) (vec O B)); auto.
Qed.
 
Lemma point_contact_k_positif :
 forall (O A O' A' B : PO) (k : R),
 k >= 0 ->
 O <> A ->
 O' <> A' ->
 vec O' B = mult_PP k (vec O B) ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B ->
 mult_PP (distance O A) (vec O' B) = mult_PP (distance O' A') (vec O B).
icercle.
assert (distance O A <> 0); auto with geo.
assert (Rsqr k = Rsqr (distance O' A' * / distance O A)).
unfold Rsqr in |- *.
assert (O <> B).
apply (isometrie_distinct (A:=O) (B:=A) (A':=O) (B':=B)); auto with geo.
assert (distance O B <> 0); auto with geo.
apply Rmult_eq_reg_l with (scalaire (vec O B) (vec O B)); auto with geo real.
replace (scalaire (vec O B) (vec O B) * (k * k)) with
 (scalaire (mult_PP k (vec O B)) (mult_PP k (vec O B))).
rewrite <- H2.
repeat rewrite carre_scalaire_distance.
rewrite H3; rewrite H4.
RReplace
 (distance O B * distance O B *
  (distance O' B * / distance O B * (distance O' B * / distance O B)))
 (distance O' B * distance O' B *
  (distance O B * / distance O B * (distance O B * / distance O B))).
RReplace (distance O B * / distance O B) 1.
ring.
Simplscal.
rewrite H2.
assert (k = distance O' A' * / distance O A).
apply Rsqr_inj; auto with real geo.
rewrite H7.
VReplace
 (mult_PP (distance O A)
    (mult_PP (distance O' A' * / distance O A) (vec O B)))
 (mult_PP (distance O' A' * (distance O A * / distance O A)) (vec O B)).
RReplace (distance O A * / distance O A) 1.
Ringvec.
Qed.
 
Lemma point_contact_k_negatif :
 forall (O A O' A' B : PO) (k : R),
 k <= 0 ->
 O <> A ->
 O' <> A' ->
 vec O' B = mult_PP k (vec O B) ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B ->
 mult_PP (distance O A) (vec O' B) = mult_PP (- distance O' A') (vec O B).
icercle.
assert (distance O A <> 0); auto with geo.
assert (Rsqr k = Rsqr (distance O' A' * / distance O A)).
unfold Rsqr in |- *.
assert (O <> B).
apply (isometrie_distinct (A:=O) (B:=A) (A':=O) (B':=B)); auto with geo.
assert (distance O B <> 0); auto with geo.
apply Rmult_eq_reg_l with (scalaire (vec O B) (vec O B)); auto with geo real.
replace (scalaire (vec O B) (vec O B) * (k * k)) with
 (scalaire (mult_PP k (vec O B)) (mult_PP k (vec O B))).
rewrite <- H2.
repeat rewrite carre_scalaire_distance.
rewrite H3; rewrite H4.
RReplace
 (distance O B * distance O B *
  (distance O' B * / distance O B * (distance O' B * / distance O B)))
 (distance O' B * distance O' B *
  (distance O B * / distance O B * (distance O B * / distance O B))).
RReplace (distance O B * / distance O B) 1.
ring.
Simplscal.
rewrite H2.
assert (- k = distance O' A' * / distance O A).
apply Rsqr_inj; auto with real geo.
rewrite <- H6; unfold Rsqr in |- *; ring.
RReplace k (- - k).
rewrite H7.
VReplace
 (mult_PP (distance O A)
    (mult_PP (- (distance O' A' * / distance O A)) (vec O B)))
 (mult_PP (- (distance O' A' * (distance O A * / distance O A))) (vec O B)).
RReplace (distance O A * / distance O A) 1.
Ringvec.
Qed.
 
Lemma point_contact_cercles_tangents :
 forall O A O' A' B : PO,
 O <> A ->
 O' <> A' ->
 alignes O B O' ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B ->
 mult_PP (distance O A) (vec O' B) = mult_PP (distance O' A') (vec O B) \/
 mult_PP (distance O A) (vec O' B) = mult_PP (- distance O' A') (vec O B).
icercle.
assert (O <> B).
apply (isometrie_distinct (A:=O) (B:=A) (A':=O) (B':=B)); auto with geo.
cut (alignes B O O'); [ intros H20 | auto with geo ].
halignes H20 ipattern:k.
absurd (B = O); auto.
assert (vec O' B = mult_PP k (vec O B)).
VReplace (vec O' B) (mult_PP (-1) (vec B O')).
rewrite H5; Ringvec.
elim (Rlt_le_dec k 0); intros.
right; try assumption.
apply point_contact_k_negatif with k; auto with real.
left; try assumption.
apply point_contact_k_positif with k; auto with real.
Qed.
 
Lemma k_negatif_barycentre :
 forall (O A O' A' B : PO) (k : R),
 k <= 0 ->
 O <> A ->
 O' <> A' ->
 vec O' B = mult_PP k (vec O B) ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B ->
 B = barycentre (cons (distance O A) O') (cons (distance O' A') O).
intros.
assert
 (mult_PP (distance O A) (vec O' B) = mult_PP (- distance O' A') (vec O B)).
apply point_contact_k_negatif with k; auto.
assert (distance O A <> 0); auto with geo.
assert (distance O' A' <> 0); auto with geo.
assert (distance O A >= 0); auto with geo.
assert (distance O' A' >= 0); auto with geo.
assert (distance O A + distance O' A' <> 0).
apply tech_Rplus; auto with geo real.
elim H9; intros; auto.
absurd (distance O' A' = 0); auto.
apply def_vecteur_bary_rec; auto.
VReplace (mult_PP (distance O' A') (vec B O))
 (mult_PP (- distance O' A') (vec O B)).
rewrite <- H5.
Ringvec.
Qed.
 
Lemma k_negatif_distance_centres :
 forall (O A O' A' B : PO) (k : R),
 k <= 0 ->
 O <> A ->
 O' <> A' ->
 vec O' B = mult_PP k (vec O B) ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B -> distance O O' = distance O A + distance O' A'.
intros.
assert (distance O A <> 0); auto with geo.
assert (distance O' A' <> 0); auto with geo.
assert (distance O A >= 0); auto with geo.
assert (distance O' A' >= 0); auto with geo.
assert (distance O A + distance O' A' <> 0).
apply tech_Rplus; auto with geo real.
elim H8; intros; auto.
absurd (distance O' A' = 0); auto.
assert (B = barycentre (cons (distance O A) O') (cons (distance O' A') O)).
apply k_negatif_barycentre with k; auto.
assert
 (mult_PP (distance O A + distance O' A') (vec O B) =
  mult_PP (distance O A) (vec O O')).
rewrite <-
 (prop_vecteur_bary (a:=distance O A) (b:=distance O' A') (A:=O') (B:=O)
    (G:=B) O); auto.
Ringvec.
assert
 (vec O O' =
  mult_PP (/ distance O A * (distance O A + distance O' A')) (vec O B)).
VReplace
 (mult_PP (/ distance O A * (distance O A + distance O' A')) (vec O B))
 (mult_PP (/ distance O A)
    (mult_PP (distance O A + distance O' A') (vec O B))).
rewrite H11.
VReplace (mult_PP (/ distance O A) (mult_PP (distance O A) (vec O O')))
 (mult_PP (distance O A * / distance O A) (vec O O')).
RReplace (distance O A * / distance O A) 1.
Ringvec.
rewrite (colinearite_distance H12).
rewrite Rabs_right; auto with real.
hcercle H3.
rewrite <- H13.
RReplace (/ distance O A * (distance O A + distance O' A') * distance O A)
 (/ distance O A * distance O A * (distance O A + distance O' A')).
RReplace (/ distance O A * distance O A) 1.
ring.
apply Rmult_pos; auto with real geo.
fourier.
Qed.
 
Lemma k_positif_vecteur_centres :
 forall (O A O' A' B : PO) (k : R),
 k >= 0 ->
 O <> A ->
 O' <> A' ->
 vec O' B = mult_PP k (vec O B) ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B ->
 vec O O' =
 mult_PP (/ distance O A * (distance O A + - distance O' A')) (vec O B).
intros.
assert
 (mult_PP (distance O A) (vec O' B) = mult_PP (distance O' A') (vec O B)).
apply point_contact_k_positif with k; auto.
assert (distance O A <> 0); auto with geo.
assert (distance O' A' <> 0); auto with geo.
assert (distance O A >= 0); auto with geo.
assert (distance O' A' >= 0); auto with geo.
assert
 (mult_PP (distance O A + - distance O' A') (vec O B) =
  mult_PP (distance O A) (vec O O')).
VReplace (mult_PP (distance O A) (vec O O'))
 (add_PP (mult_PP (distance O A) (vec O B))
    (mult_PP (-1) (mult_PP (distance O A) (vec O' B)))).
rewrite H5.
Ringvec.
VReplace
 (mult_PP (/ distance O A * (distance O A + - distance O' A')) (vec O B))
 (mult_PP (/ distance O A)
    (mult_PP (distance O A + - distance O' A') (vec O B))).
rewrite H10.
VReplace (mult_PP (/ distance O A) (mult_PP (distance O A) (vec O O')))
 (mult_PP (distance O A * / distance O A) (vec O O')).
RReplace (distance O A * / distance O A) 1.
Ringvec.
Qed.
 
Lemma k_positif_distance_centres :
 forall (O A O' A' B : PO) (k : R),
 k >= 0 ->
 O <> A ->
 O' <> A' ->
 vec O' B = mult_PP k (vec O B) ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B ->
 distance O O' = Rabs (distance O A + - distance O' A').
intros.
assert (distance O A <> 0); auto with geo.
assert
 (vec O O' =
  mult_PP (/ distance O A * (distance O A + - distance O' A')) (vec O B)).
apply k_positif_vecteur_centres with k; auto.
rewrite (colinearite_distance H6).
rewrite Rabs_mult.
rewrite Rabs_right; auto with real geo.
hcercle H3.
rewrite <- H7.
RReplace
 (/ distance O A * Rabs (distance O A + - distance O' A') * distance O A)
 (/ distance O A * distance O A * Rabs (distance O A + - distance O' A')).
RReplace (/ distance O A * distance O A) 1.
ring.
Qed.
 
Lemma aux_Rpos :
 forall a b : R, a >= 0 -> b >= 0 -> a + b = Rabs (a + - b) -> a = 0 \/ b = 0.
intros.
assert (Rsqr (a + b) = Rsqr (a + - b)).
rewrite H1.
rewrite <- Rsqr_abs; auto.
apply Rmult_integral.
assert (4 * (a * b) = 0).
RReplace (4 * (a * b)) (2 * a * (2 * b)).
RReplace (2 * a) (a + b + (a + - b)).
RReplace (2 * b) (a + b - (a + - b)).
rewrite Rsqr_plus_minus.
rewrite H2; auto with real.
assert (4 <> 0); auto with real.
elim Rmult_integral with (r1 := 4) (r2 := a * b);
 [ intros H5; try clear without_div_Od
 | intros H5; try clear without_div_Od; try exact H5
 | auto ].
absurd (4 = 0); auto.
Qed.
 
Theorem cercles_tangents_contact_unique :
 forall O A O' A' B C : PO,
 O <> A ->
 O' <> A' ->
 ~ cercle_rayon O A A' ->
 alignes O B O' ->
 cercle_rayon O A B ->
 cercle_rayon O' A' B ->
 alignes O C O' -> cercle_rayon O A C -> cercle_rayon O' A' C -> B = C.
intros O A O' A' B C H H0 H100 H1 H2 H3 H4 H5 H6; try assumption.
assert (O <> B).
apply (isometrie_distinct (A:=O) (B:=A) (A':=O) (B':=B)); auto with geo.
assert (O <> C).
apply (isometrie_distinct (A:=O) (B:=A) (A':=O) (B':=C)); auto with geo.
assert (alignes B O O'); auto with geo.
halignes H9 ipattern:x.
absurd (B = O); auto.
assert (vec O' B = mult_PP x (vec O B)).
VReplace (vec O' B) (mult_PP (-1) (vec B O')).
rewrite H10; Ringvec.
assert (alignes C O O'); auto with geo.
halignes H12 ipattern:k.
absurd (C = O); auto.
assert (vec O' C = mult_PP k (vec O C)).
VReplace (vec O' C) (mult_PP (-1) (vec C O')).
rewrite H13; Ringvec.
assert (distance O A <> 0); auto with geo.
assert (distance O' A' <> 0); auto with geo.
assert (distance O A >= 0); auto with geo.
assert (distance O' A' >= 0); auto with geo.
assert (distance O A + distance O' A' <> 0).
apply tech_Rplus; auto with geo real.
elim H18; intros; auto.
absurd (distance O' A' = 0); auto.
elim (Rlt_le_dec x 0); intros.
assert (x <= 0); auto with real.
assert (B = barycentre (cons (distance O A) O') (cons (distance O' A') O)).
apply k_negatif_barycentre with x; auto.
elim (Rlt_le_dec k 0); intros.
assert (k <= 0); auto with real.
assert (C = barycentre (cons (distance O A) O') (cons (distance O' A') O)).
apply k_negatif_barycentre with k; auto.
rewrite H21; auto.
assert (distance O O' = distance O A + distance O' A').
apply k_negatif_distance_centres with (4 := H11); auto.
assert (distance O O' = Rabs (distance O A + - distance O' A')).
apply k_positif_distance_centres with (4 := H14); auto.
auto with real.
assert (distance O A = 0 \/ distance O' A' = 0).
apply aux_Rpos; auto.
rewrite <- H23; auto.
elim H24; intros.
absurd (distance O A = 0); auto.
absurd (distance O' A' = 0); auto.
assert (distance O O' = Rabs (distance O A + - distance O' A')).
apply k_positif_distance_centres with (4 := H11); auto.
auto with real.
elim (classic (distance O A = distance O' A')); intros.
assert (O = O').
assert (distance O O' = 0); auto with geo.
rewrite H20; rewrite H21.
RReplace (distance O' A' + - distance O' A') 0.
rewrite Rabs_right; auto with real.
absurd (cercle_rayon O A A'); auto.
icercle.
rewrite H21; rewrite H22; auto.
assert
 (mult_PP (distance O A + - distance O' A') (vec O B) =
  mult_PP (distance O A) (vec O O')).
VReplace (mult_PP (distance O A) (vec O O'))
 (add_PP (mult_PP (distance O A) (vec O B))
    (mult_PP (-1) (mult_PP (distance O A) (vec O' B)))).
assert
 (mult_PP (distance O A) (vec O' B) = mult_PP (distance O' A') (vec O B)).
apply point_contact_k_positif with x; auto.
auto with real.
rewrite H22; Ringvec.
assert (distance O A + - distance O' A' <> 0); auto with real.
elim (Rlt_le_dec k 0); intros.
assert (k <= 0); auto with real.
assert (distance O O' = distance O A + distance O' A').
apply k_negatif_distance_centres with (4 := H14); auto.
assert (distance O A = 0 \/ distance O' A' = 0).
apply aux_Rpos; auto.
rewrite <- H25; auto.
elim H26; intros.
absurd (distance O A = 0); auto.
absurd (distance O' A' = 0); auto.
assert
 (mult_PP (distance O A + - distance O' A') (vec O C) =
  mult_PP (distance O A) (vec O O')).
VReplace (mult_PP (distance O A) (vec O O'))
 (add_PP (mult_PP (distance O A) (vec O C))
    (mult_PP (-1) (mult_PP (distance O A) (vec O' C)))).
assert
 (mult_PP (distance O A) (vec O' C) = mult_PP (distance O' A') (vec O C)).
apply point_contact_k_positif with k; auto.
auto with real.
rewrite H24; Ringvec.
apply egalite_vecteur_point with O.
assert
 (vec O B =
  mult_PP (/ (distance O A + - distance O' A'))
    (mult_PP (distance O A) (vec O O'))).
rewrite <- H22.
VReplace
 (mult_PP (/ (distance O A + - distance O' A'))
    (mult_PP (distance O A + - distance O' A') (vec O B)))
 (mult_PP
    ((distance O A + - distance O' A') * / (distance O A + - distance O' A'))
    (vec O B)).
replace
 ((distance O A + - distance O' A') * / (distance O A + - distance O' A'))
 with 1; auto with real.
Ringvec.
rewrite H25.
rewrite <- H24.
VReplace
 (mult_PP (/ (distance O A + - distance O' A'))
    (mult_PP (distance O A + - distance O' A') (vec O C)))
 (mult_PP
    ((distance O A + - distance O' A') * / (distance O A + - distance O' A'))
    (vec O C)).
replace
 ((distance O A + - distance O' A') * / (distance O A + - distance O' A'))
 with 1; auto with real.
Ringvec.
Qed.