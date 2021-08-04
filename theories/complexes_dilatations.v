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
Require Export operations_complexes.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma angle_argument :
 forall (z z' : C) (M M' : PO),
 O <> M :>PO ->
 O <> M' :>PO ->
 z = affixe M :>C ->
 z' = affixe M' :>C ->
 cons_AV (vec O M) (vec O M') = plus (argument z') (opp (argument z)) :>AV.
intros.
rewrite (argument_def2 (M:=M) (z:=z)); auto.
rewrite (argument_def2 (M:=M') (z:=z')); auto.
rewrite Chasles_diff; auto with geo.
Qed.
Hint Resolve angle_argument: geo.
 
Lemma egalite_vecteur_OM_image :
 forall (z z' : C) (M M' : PO),
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C -> vec O M = vec O M' :>PP -> z = z' :>C.
intros.
apply egalite_point_image with (M := M) (M' := M'); eauto with geo.
apply vecteur_nul_conf.
replace (vec M M') with (add_PP (vec O M') (mult_PP (-1) (vec O M)));
 [ idtac | Ringvec ].
rewrite H1; Ringvec.
Qed.
 
Lemma egalite_vecteur_image :
 forall (z z' : C) (A B A' B' : PO),
 z = affixe_vec (vec A B) :>C ->
 z' = affixe_vec (vec A' B') :>C -> vec A B = vec A' B' :>PP -> z = z' :>C.
intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 intros D H2; intros; try exact H2.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros D'; intros; try exact H2.
apply egalite_vecteur_OM_image with (M := D) (M' := D').
rewrite H2; auto.
rewrite H3; auto.
rewrite H2; rewrite H3; auto.
Qed.
 
Lemma egalite_affixe_vecteur_OM :
 forall (z z' : C) (M M' : PO),
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C -> z = z' :>C -> vec O M = vec O M' :>PP.
intros.
replace M' with M; auto.
apply egalite_affixe_point with (3 := H1); auto with geo.
Qed.
 
Lemma egalite_affixe_vecteur :
 forall (z z' : C) (A B A' B' : PO),
 z = affixe_vec (vec A B) :>C ->
 z' = affixe_vec (vec A' B') :>C -> z = z' :>C -> vec A B = vec A' B' :>PP.
intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 intros D H2; intros; try exact H2.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros D'; intros; try exact H2.
rewrite <- H2; rewrite <- H3.
apply egalite_affixe_vecteur_OM with (z := z) (z' := z'); auto.
rewrite H2; auto.
rewrite H3; auto.
Qed.
Hint Resolve affixe_vec_AB: geo.
 
Lemma complexe_translation :
 forall (a z z' : C) (A M M' : PO),
 z = affixe M ->
 z' = affixe M' ->
 a = affixe A -> z' = Cplus z a -> M' = translation O A M :>PO.
intros.
apply rec_translation_vecteur.
apply
 (egalite_affixe_vecteur (z:=a) (z':=Cplus z' (Copp z)) (A:=O) (B:=A) (A':=M)
    (B':=M')); auto with geo.
rewrite H2.
ring.
Qed.
 
Lemma rec_complexe_translation :
 forall (a z z' : C) (A M M' : PO),
 z = affixe M ->
 z' = affixe M' ->
 a = affixe A -> M' = translation O A M :>PO -> z' = Cplus z a.
intros.
cut (Cplus z' (Copp z) = a); intros.
rewrite <- H3; ring.
apply
 (egalite_vecteur_image (z:=Cplus z' (Copp z)) (z':=a) (A:=M) (B:=M') (A':=O)
    (B':=A)); auto with geo.
symmetry  in |- *; apply translation_vecteur; auto.
Qed.
 
Ltac paffixe M z := elim (existence_affixe_point M); intros z; intros.
 
Lemma argument_affixe_produit_positif_vecteur_OM :
 forall (k : R) (M M' : PO) (z z' : C),
 O <> M :>PO ->
 k > 0 ->
 vec O M' = mult_PP k (vec O M) :>PP ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C -> argument z' = argument z :>AV.
intros.
cut (O <> M'); intros.
rewrite (argument_def2 (M:=M) (z:=z)); auto with geo.
rewrite (argument_def2 (M:=M') (z:=z')); auto with geo.
apply angle_produit_positif_r with k; auto with geo.
apply distinct_produit_vecteur with (3 := H1); auto.
auto with real.
Qed.
 
Lemma argument_affixe_produit_negatif_vecteur_OM :
 forall (k : R) (M M' : PO) (z z' : C),
 O <> M :>PO ->
 k < 0 ->
 vec O M' = mult_PP k (vec O M) :>PP ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 argument z' = plus (argument z) (image_angle pi) :>AV.
intros.
cut (O <> M'); intros.
rewrite (argument_def2 (M:=M) (z:=z)); auto with geo.
rewrite (argument_def2 (M:=M') (z:=z')); auto with geo.
apply angle_produit_negatif_r with k; auto with geo.
apply distinct_produit_vecteur with (3 := H1); auto.
auto with real.
Qed.
 
Lemma argument_affixe_produit_positif_vecteur :
 forall (k : R) (A B A' B' : PO) (z z' : C),
 A <> B :>PO ->
 k > 0 ->
 vec A' B' = mult_PP k (vec A B) :>PP ->
 z = affixe_vec (vec A B) :>C ->
 z' = affixe_vec (vec A' B') :>C -> argument z' = argument z :>AV.
intros k A B A' B' z z' H H0; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B); intros M;
 intros H1.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros M'; intros H2.
rewrite <- H2; rewrite <- H1; intros.
apply
 (argument_affixe_produit_positif_vecteur_OM (k:=k) (M:=M) (M':=M') (z:=z)
    (z':=z')); auto.
apply distinct_egalite_vecteur with (2 := H1); auto.
Qed.
 
Lemma argument_affixe_produit_negatif_vecteur :
 forall (k : R) (A B A' B' : PO) (z z' : C),
 A <> B :>PO ->
 k < 0 ->
 vec A' B' = mult_PP k (vec A B) :>PP ->
 z = affixe_vec (vec A B) :>C ->
 z' = affixe_vec (vec A' B') :>C ->
 argument z' = plus (argument z) (image_angle pi) :>AV.
intros k A B A' B' z z' H H0; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B); intros M;
 intros H1.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros M'; intros H2.
rewrite <- H2; rewrite <- H1; intros.
apply
 (argument_affixe_produit_negatif_vecteur_OM (k:=k) (M:=M) (M':=M') (z:=z)
    (z':=z')); auto.
apply distinct_egalite_vecteur with (2 := H1); auto.
Qed.
 
Lemma module_affixe_produit_vecteur_OM :
 forall (k : R) (M M' : PO) (z z' : C),
 vec O M' = mult_PP k (vec O M) :>PP ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C -> module z' = Rabs k * module z.
intros.
rewrite (module_def2 (z:=z) (M:=M)); auto with geo.
rewrite (module_def2 (z:=z') (M:=M')); auto with geo.
Qed.
 
Lemma module_affixe_produit_vecteur :
 forall (k : R) (A B A' B' : PO) (z z' : C),
 vec A' B' = mult_PP k (vec A B) :>PP ->
 z = affixe_vec (vec A B) :>C ->
 z' = affixe_vec (vec A' B') :>C -> module z' = Rabs k * module z.
intros k A B A' B' z z'; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B); intros M;
 intros H1.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros M'; intros H2.
rewrite <- H2; rewrite <- H1; intros.
apply
 (module_affixe_produit_vecteur_OM (k:=k) (M:=M) (M':=M') (z:=z) (z':=z'));
 auto.
Qed.
 
Lemma egalite_point_zeroC :
 forall (z : C) (A B : PO),
 A = B -> z = affixe_vec (vec A B) :>C -> z = zeroC :>C.
intros z A B H; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 intros M H1.
rewrite <- H1; intros.
cut (O = M); intros; auto.
rewrite <- H2 in H0.
rewrite affixe_origine; auto with geo.
apply vecteur_nul_conf.
rewrite H1; rewrite H; Ringvec.
Qed.
 
Lemma points_distincts_non_zeroC :
 forall (z : C) (A B : PO),
 A <> B :>PO -> z = affixe_vec (vec A B) :>C -> z <> zeroC :>C.
intros z A B H; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 intros M H1.
rewrite <- H1; intros.
cut (O <> M); intros.
apply nonorigine_image_nonzero with M; auto with geo.
red in |- *; intros; apply H.
apply vecteur_nul_conf.
rewrite <- H1; rewrite H2; Ringvec.
Qed.
 
Theorem produit_vecteur_image :
 forall (k : R) (z z' : C) (A B A' B' : PO),
 z = affixe_vec (vec A B) :>C ->
 z' = affixe_vec (vec A' B') :>C ->
 vec A' B' = mult_PP k (vec A B) :>PP -> z' = Cmult (Rinj k) z :>C.
intros.
cut (module z' = Rabs k * module z); intros.
2: apply
    (module_affixe_produit_vecteur (k:=k) (A:=A) (B:=B) (A':=A') (B':=B')
       (z:=z) (z':=z')); auto.
discrimine A B.
rewrite (egalite_point_zeroC (z:=z) (A:=A) (B:=B)); auto with geo.
rewrite (egalite_point_zeroC (z:=z') (A:=A') (B:=B')); auto with geo.
apply vecteur_nul_conf.
rewrite H1; rewrite H3; Ringvec.
elim (classic (k = 0)); intros.
rewrite (egalite_point_zeroC (z:=z') (A:=A') (B:=B')); auto with geo.
rewrite H4; rewrite Rinj_zero; ring.
apply vecteur_nul_conf.
rewrite H1; rewrite H4; Ringvec.
cut (A' <> B'); intros.
cut (k > 0 \/ k < 0); intros.
elim H6; [ intros H7; try clear H6 | intros H7; try clear H6; try exact H7 ].
cut (argument z' = argument z); intros.
2: apply
    (argument_affixe_produit_positif_vecteur (k:=k) (A:=A) (B:=B) (A':=A')
       (B':=B') (z:=z) (z':=z')); auto with geo.
apply egalite_forme_polaire.
apply points_distincts_non_zeroC with (1 := H5); auto.
apply nonzero_produit; auto with geo.
apply points_distincts_non_zeroC with (1 := H3); auto with geo.
rewrite H2; rewrite Cmult_module; rewrite module_reel; auto.
rewrite H6; rewrite Cmult_argument; auto with geo.
rewrite argument_reel_pos; auto.
rewrite plus_commutative; symmetry  in |- *; rewrite plus_angle_zero; auto.
apply points_distincts_non_zeroC with (1 := H3); auto with geo.
cut (argument z' = plus (argument z) (image_angle pi)); intros.
2: apply
    (argument_affixe_produit_negatif_vecteur (k:=k) (A:=A) (B:=B) (A':=A')
       (B':=B') (z:=z) (z':=z')); auto with geo.
apply egalite_forme_polaire.
apply points_distincts_non_zeroC with (1 := H5); auto.
apply nonzero_produit; auto with geo.
apply points_distincts_non_zeroC with (1 := H3); auto with geo.
rewrite H2; rewrite Cmult_module; rewrite module_reel; auto.
rewrite H6; rewrite Cmult_argument; auto with geo.
rewrite argument_reel_neg; auto.
rewrite plus_commutative; auto.
apply points_distincts_non_zeroC with (1 := H3); auto with geo.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H6; try clear total_order
 | intros H6;
    (elim H6;
      [ intros H7; try clear H6 total_order
      | intros H7; try clear H6 total_order; try exact H7 ]) ].
right; try assumption.
absurd (k = 0); auto.
left; try assumption.
apply distinct_mult_vecteur with (3 := H1); auto.
Qed.
 
Theorem produit_reel_affixe_vecteur_OM :
 forall (k : R) (z z' : C) (M M' : PO),
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 z' = Cmult (Rinj k) z :>C -> vec O M' = mult_PP k (vec O M) :>PP.
intros.
cut (module z' = module (Rinj k) * module z); intros.
discrimine O M.
cut (z = zeroC); intros.
replace M with M'.
Ringvec.
apply (egalite_affixe_point (z:=z') (z':=z) (M:=M') (M':=M)); auto with geo.
rewrite H1; rewrite H4; ring.
apply (egalite_point_image (z:=z) (z':=zeroC) (M:=M) (M':=O)); auto with geo.
cut (z <> zeroC); [ idtac | eauto with geo ].
intros H20.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H6; try clear total_order
 | intros H6;
    (elim H6;
      [ intros H7; try clear H6 | intros H7; try clear H6; try exact H7 ]) ].
rewrite module_reel_neg in H2; auto with real.
cut (k <> 0); intros; [ idtac | auto with real ].
cut (z' <> zeroC); intros.
cut (O <> M'); intros.
cut (cons_AV (vec O M) (vec O M') = image_angle pi); intros.
rewrite (alignes_distance_negatif_colineaire (k:=- k) (A:=O) (B:=M) (C:=M'));
 auto with geo.
replace (- - k) with k; try ring; auto.
rewrite <- (module_def2 (z:=z) (M:=M)); auto with geo.
rewrite <- (module_def2 (z:=z') (M:=M')); auto with geo.
rewrite (angle_argument (z:=z) (z':=z') (M:=M) (M':=M')); auto with geo.
rewrite H1; rewrite Cmult_argument; auto with geo.
rewrite argument_reel_neg; auto with geo.
elim existence_argument with (z := z);
 [ intros; try clear existence_argument | auto with geo ].
rewrite H8; rewrite <- mes_opp; repeat rewrite <- add_mes_compatible.
replace (pi + x + - x) with pi; [ auto | ring ].
apply image_nonzero_nonorigine with z'; auto with geo.
apply nonzero_module.
rewrite H2.
apply Rmult_integral_contrapositive.
split; auto with real geo.
cut (z' = zeroC); intros.
replace M' with O.
rewrite H7; Ringvec.
apply (egalite_affixe_point (z:=zeroC) (z':=z') (M:=O) (M':=M'));
 auto with geo.
apply module_nul_zeroC.
rewrite H2; rewrite H7.
replace (Rinj 0) with zeroC; auto with geo.
rewrite module_zeroC; ring.
rewrite module_reel_pos in H2; auto with real.
cut (k <> 0); intros; [ idtac | auto with real ].
cut (z' <> zeroC); intros.
cut (O <> M'); intros.
cut (cons_AV (vec O M) (vec O M') = image_angle 0); intros.
rewrite (alignes_distance_positif_colineaire (k:=k) (A:=O) (B:=M) (C:=M'));
 auto with geo.
rewrite <- (module_def2 (z:=z) (M:=M)); auto with geo.
rewrite <- (module_def2 (z:=z') (M:=M')); auto with geo.
rewrite (angle_argument (z:=z) (z':=z') (M:=M) (M':=M')); auto with geo.
rewrite H1; rewrite Cmult_argument; auto with geo.
rewrite argument_reel_pos; auto with geo.
elim existence_argument with (z := z);
 [ intros; try clear existence_argument | auto with geo ].
rewrite H8; rewrite <- mes_opp; repeat rewrite <- add_mes_compatible.
replace (0 + x + - x) with 0; [ auto | ring ].
apply image_nonzero_nonorigine with z'; auto with geo.
apply nonzero_module.
rewrite H2.
apply Rmult_integral_contrapositive.
split; auto with real geo.
rewrite H1; rewrite Cmult_module; auto.
Qed.
 
Theorem produit_reel_affixe_vecteur :
 forall (k : R) (z z' : C) (A B A' B' : PO),
 z = affixe_vec (vec A B) :>C ->
 z' = affixe_vec (vec A' B') :>C ->
 z' = Cmult (Rinj k) z :>C -> vec A' B' = mult_PP k (vec A B) :>PP.
intros k z z' A B A' B'; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B); intros M;
 intros H1.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros M'; intros H2.
rewrite <- H2; rewrite <- H1; intros.
apply (produit_reel_affixe_vecteur_OM (k:=k) (z:=z) (z':=z') (M:=M) (M':=M'));
 auto.
Qed.
 
Theorem complexe_homothetie :
 forall (k : R) (j z z' : C) (J M M' : PO),
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 Cplus z' (Copp j) = Cmult (Rinj k) (Cplus z (Copp j)) ->
 M' = homothetie k J M :>PO.
intros.
apply vecteur_homothetie.
apply produit_reel_affixe_vecteur with (3 := H2); auto with geo.
Qed.
 
Theorem rec_complexe_homothetie :
 forall (k : R) (j z z' : C) (J M M' : PO),
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 M' = homothetie k J M :>PO ->
 Cplus z' (Copp j) = Cmult (Rinj k) (Cplus z (Copp j)).
intros.
cut (vec J M' = mult_PP k (vec J M)); intros.
2: apply homothetie_vecteur; auto.
apply produit_vecteur_image with (3 := H3); auto with geo.
Qed.