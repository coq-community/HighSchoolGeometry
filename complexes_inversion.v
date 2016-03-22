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


Require Export inversion.
Require Export complexes_conjugaison.
Require Export complexes_similitudes.
Set Implicit Arguments.
Unset Strict Implicit.
(* a mettre plus haut dans les complexes*)
 
Lemma Rinj_opp : forall k : R, Rinj (- k) = Copp (Rinj k).
unfold Rinj in |- *; intros.
rewrite Copp_algebrique.
RReplace (-0) 0; auto.
Qed.
 
Lemma Conj_Copp : forall z : C, Conj (Copp z) = Copp (Conj z).
intros.
elim existence_parties_relles_imaginaires with (z := z); intros x1 H; elim H;
 intros y1 H0; try clear H; try exact H0.
rewrite H0.
rewrite Copp_algebrique.
repeat rewrite Conj_algebrique.
rewrite Copp_algebrique; auto.
Qed.
 
Lemma Copp_Cmult : forall z : C, Copp z = Cmult (Rinj (-1)) z.
intros.
replace (Rinj (-1)) with (Copp oneC).
ring.
unfold oneC, Rinj in |- *.
rewrite Copp_algebrique; auto.
RReplace (-0) 0; auto.
Qed.
 
Lemma Copp_non_zeroC : forall z : C, z <> zeroC -> Copp z <> zeroC.
intros.
rewrite Copp_Cmult.
apply nonzero_produit; auto with geo.
Qed.
Hint Resolve Copp_non_zeroC nonzero_produit: geo.
 
Lemma Cinv_Copp : forall z : C, z <> zeroC -> Cinv (Copp z) = Copp (Cinv z).
intros.
assert (Copp z <> zeroC); auto with geo.
assert (Cmult (Copp z) (Copp (Cinv z)) = oneC).
2: apply Cinv_def2; auto.
ring_simplify.
apply Cinv_def; auto.
Qed.
 
Lemma carre_module :
 forall (z : C) (x y : R),
 z = cons_cart x y -> Rsqr (module z) = Rsqr x + Rsqr y.
intros.
rewrite (passage_algebrique_module H).
rewrite Rsqr_sqrt; auto.
assert (0 <= Rsqr x); auto with real.
assert (0 <= Rsqr y); auto with real.
fourier.
Qed.
 
Lemma produit_Conj_module :
 forall z : C, Cmult z (Conj z) = Rinj (Rsqr (module z)).
intros.
elim existence_parties_relles_imaginaires with (z := z); intros x H; elim H;
 intros y H0; try clear H; try exact H0.
pattern z at 1 2 in |- *.
rewrite H0.
rewrite Conj_algebrique.
rewrite (passage_algebrique_module H0).
rewrite Cmult_algebrique.
RReplace (y * x + x * - y) 0.
rewrite Rsqr_sqrt.
unfold Rsqr, Rinj in |- *.
RReplace (x * x + - (y * - y)) (x * x + y * y); auto.
assert (0 <= Rsqr x); auto with real.
assert (0 <= Rsqr y); auto with real.
fourier.
Qed.
 
Lemma Rinj_Cmult : forall x y : R, Rinj (x * y) = Cmult (Rinj x) (Rinj y).
intros.
unfold Rinj, oneC in |- *.
rewrite Cmult_algebrique.
RReplace (x * y + - (0 * 0)) (x * y).
RReplace (0 * y + x * 0) 0; auto.
Qed.
 
Lemma Rinj_Cinv : forall k : R, k <> 0 -> Rinj (/ k) = Cinv (Rinj k).
intros.
assert (Rinj k <> zeroC); auto with geo.
assert (Cmult (Rinj k) (Rinj (/ k)) = oneC).
2: symmetry  in |- *; apply Cinv_def2; auto.
unfold Rinj, oneC in |- *.
rewrite Cmult_algebrique.
replace (0 * / k + k * 0) with 0 by (field;auto).
replace (k * / k + - (0 * 0)) with 1 by (field;auto).
auto.
Qed.

Lemma Cinv_Cmult :
 forall z z' : C,
 z <> zeroC -> z' <> zeroC -> Cinv (Cmult z z') = Cmult (Cinv z) (Cinv z').
intros.
assert (Cmult z z' <> zeroC); [ auto with geo | idtac ].
assert (Cmult (Cmult z z') (Cmult (Cinv z) (Cinv z')) = oneC).
replace (Cmult (Cmult z z') (Cmult (Cinv z) (Cinv z'))) with
 (Cmult (Cmult z (Cinv z)) (Cmult z' (Cinv z'))); [ idtac | ring ].
rewrite Cinv_def; auto.
rewrite Cinv_def; auto.
ring.
apply Cinv_def2; auto.
Qed.
 
Lemma Cinv_Conj :
 forall z : C,
 z <> zeroC -> Cinv z = Cmult (Cinv (Rinj (Rsqr (module z)))) (Conj z).
intros.
assert (module z <> 0); auto with geo.
assert (Rsqr (module z) <> 0).
unfold Rsqr in |- *; auto with real.
assert (Rinj (Rsqr (module z)) <> zeroC); auto with geo.
assert (Cmult z (Cmult (Cinv (Rinj (Rsqr (module z)))) (Conj z)) = oneC).
2: apply Cinv_def2; auto.
replace (Cmult z (Cmult (Cinv (Rinj (Rsqr (module z)))) (Conj z))) with
 (Cmult (Cinv (Rinj (Rsqr (module z)))) (Cmult z (Conj z))).
rewrite produit_Conj_module.
apply Cinv_l; auto.
ring.
Qed.
 
Lemma Conj_Cinv :
 forall z : C,
 z <> zeroC -> Cinv (Conj z) = Cmult (Cinv (Rinj (Rsqr (module z)))) z.
intros.
assert (Conj z <> zeroC); auto with geo.
rewrite Cinv_Conj; auto.
rewrite Conj_Conj; rewrite module_Conj; auto.
Qed.
 
Lemma Cmult_Rinj_algebrique :
 forall x y k : R, Cmult (Rinj k) (cons_cart x y) = cons_cart (k * x) (k * y).
unfold Rinj in |- *; intros.
rewrite Cmult_algebrique.
replace (k * x + - (0 * y)) with (k * x) by ring.
replace (0 * x + k * y) with (k * y) by ring.
auto.
Qed.
 
Lemma Cinv_algebrique :
 forall (z : C) (x y : R),
 z <> zeroC ->
 z = cons_cart x y ->
 Cinv z = cons_cart (x / (Rsqr x + Rsqr y)) (- y / (Rsqr x + Rsqr y)).
intros.
assert (module z <> 0); auto with geo.
assert (Rsqr (module z) <> 0).
unfold Rsqr in |- *; auto with real.
rewrite Cinv_Conj; auto.
rewrite (Conj_def H0); auto.
rewrite <- Rinj_Cinv; auto.
rewrite Cmult_Rinj_algebrique.
rewrite (carre_module H0); auto.
unfold Rdiv in |- *.
RReplace (/ (Rsqr x + Rsqr y) * x) (x * / (Rsqr x + Rsqr y)).
RReplace (/ (Rsqr x + Rsqr y) * - y) (- y * / (Rsqr x + Rsqr y)); auto.
Qed.
(* partie concernant l'inversion *)
 
Lemma inversion_origine_module :
 forall (k : R) (z z' : C) (M M' : PO),
 k <> 0 ->
 O <> M ->
 z = affixe_vec (vec O M) ->
 z' = affixe_vec (vec O M') ->
 M' = inversion O k M :>PO -> module z' = Rabs k * / module z.
intros.
assert (vec O M' = mult_PP (/ Rsqr (distance O M) * k) (vec O M)).
apply inversion_pole_vecteur; auto.
assert (module z <> 0).
apply module_non_zero.
apply points_distincts_non_zeroC with (1 := H0); auto with geo.
RReplace (/ module z) (1 * / module z).
RReplace 1 (/ module z * module z).
RReplace (/ module z * module z * / module z)
 (/ module z * / module z * module z).
replace (/ module z * / module z) with (/ Rsqr (module z)).
pattern (module z) at 1 in |- *.
rewrite (module_def2 (z:=z) (M:=M)); auto with geo.
RReplace (Rabs k * (/ Rsqr (distance O M) * module z))
 (/ Rsqr (distance O M) * Rabs k * module z).
replace (/ Rsqr (distance O M) * Rabs k) with
 (Rabs (/ Rsqr (distance O M) * k)).
apply
 (module_affixe_produit_vecteur_OM (k:=/ Rsqr (distance O M) * k) (M:=M)
    (M':=M') (z:=z) (z':=z')); auto with geo.
rewrite Rabs_mult.
rewrite <- (module_def2 (z:=z) (M:=M)); auto with geo.
unfold Rsqr in |- *.
rewrite Rabs_Rinv; auto with real.
rewrite Rabs_right; auto with geo real.
unfold Rsqr in |- *.
rewrite Rinv_mult_distr; auto with real.
Qed.
 
Lemma aux_positif :
 forall (k : R) (M : PO),
 O <> M :>PO -> k > 0 -> / Rsqr (distance O M) * k > 0.
intros.
apply Rmult_gt_0_compat; auto.
apply Rgt_inv; auto.
unfold Rsqr in |- *.
assert (distance O M > 0).
assert (distance O M >= 0); auto with geo.
elim H1; intros; auto.
absurd (distance O M = 0); auto with geo.
apply Rmult_gt_0_compat; auto.
Qed.
 
Lemma aux_negatif :
 forall (k : R) (M : PO),
 O <> M :>PO -> k < 0 -> / Rsqr (distance O M) * k < 0.
intros.
RReplace (/ Rsqr (distance O M) * k) (- (/ Rsqr (distance O M) * - k)).
apply Ropp_lt_gt_0_contravar.
apply aux_positif; auto with real.
Qed.
 
Lemma argument_affixe_inversion_pole_positif :
 forall (k : R) (M M' : PO) (z z' : C),
 O <> M :>PO ->
 k > 0 ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 M' = inversion O k M :>PO -> argument z' = argument z :>AV.
intros.
assert (vec O M' = mult_PP (/ Rsqr (distance O M) * k) (vec O M)).
apply inversion_pole_vecteur; auto.
auto with real.
apply argument_affixe_produit_positif_vecteur_OM with (3 := H4); auto.
apply aux_positif; auto.
Qed.
 
Lemma argument_affixe_inversion_pole_negatif :
 forall (k : R) (M M' : PO) (z z' : C),
 O <> M :>PO ->
 k < 0 ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 M' = inversion O k M :>PO ->
 argument z' = plus (argument z) (image_angle pi) :>AV.
intros.
assert (vec O M' = mult_PP (/ Rsqr (distance O M) * k) (vec O M)).
apply inversion_pole_vecteur; auto.
auto with real.
apply argument_affixe_produit_negatif_vecteur_OM with (3 := H4); auto.
apply aux_negatif; auto.
Qed.
 
Lemma argument_affixe_inversion_positif_conjugue :
 forall (k : R) (M M' : PO) (z z' : C),
 O <> M :>PO ->
 k > 0 ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 M' = inversion O k M :>PO -> argument z' = argument (Cinv (Conj z)) :>AV.
intros.
assert (z <> zeroC).
apply points_distincts_non_zeroC with (1 := H); auto with geo.
assert (Conj z <> zeroC); auto with geo.
rewrite
 (argument_affixe_inversion_pole_positif (k:=k) (M:=M) (M':=M') (z:=z)
    (z':=z')); auto.
rewrite Cinv_argument; auto.
rewrite argument_Conj2; auto.
mes (argument z).
RReplace (- - x) x; auto.
Qed.
 
Theorem inversion_positif_complexe :
 forall (k : R) (z z' : C) (M M' : PO),
 O <> M :>PO ->
 k > 0 ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 M' = inversion O k M :>PO -> z' = Cmult (Rinj k) (Cinv (Conj z)).
intros.
assert (k <> 0); auto with real.
assert (z <> zeroC).
apply points_distincts_non_zeroC with (1 := H); auto with geo.
assert (Conj z <> zeroC); auto with geo.
assert (O <> M').
apply image_distinct_pole with (3 := H3); auto with real.
apply egalite_forme_polaire.
apply points_distincts_non_zeroC with (1 := H7); auto with geo.
apply nonzero_produit; auto with geo.
rewrite (inversion_origine_module (k:=k) (z:=z) (z':=z') (M:=M) (M':=M'));
 auto.
rewrite <- (module_Conj z).
rewrite Cmult_module; auto.
rewrite Cinv_module; auto.
rewrite module_reel; auto.
rewrite
 (argument_affixe_inversion_positif_conjugue (k:=k) (M:=M) (M':=M') (z:=z)
    (z':=z')); auto.
rewrite Cmult_argument; auto with geo.
rewrite argument_reel_pos; auto with real.
mes (argument (Cinv (Conj z))).
RReplace (0 + x) x; auto.
Qed.
 
Theorem inversion_negatif_complexe :
 forall (k : R) (z z' : C) (M M' : PO),
 O <> M :>PO ->
 k < 0 ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 M' = inversion O k M :>PO -> z' = Cmult (Rinj k) (Cinv (Conj z)).
intros.
assert (k <> 0); auto with real.
assert (z <> zeroC).
apply points_distincts_non_zeroC with (1 := H); auto with geo.
assert (Conj z <> zeroC); auto with geo.
symetrique O M ipattern:N.
assert (M' = inversion O (- k) N).
apply inversion_oppose_puissance with (3 := H3); auto.
assert (- k > 0); auto with real.
assert (O <> N).
assert (O = homothetie (-1) O O); auto with geo.
unfold symetrie in H5.
apply
 (image_homothetie_distincts (k:=-1) (I:=O) (A:=O) (A':=O) (B:=M) (B':=N));
 auto with real.
rewrite
 (inversion_positif_complexe (k:=- k) (z:=Copp z) (z':=z') (M:=N) (M':=M'))
 ; auto.
rewrite Rinj_opp.
rewrite Conj_Copp.
rewrite Cinv_Copp; auto.
ring.
symmetry  in |- *.
rewrite
 (produit_vecteur_image (k:=-1) (z:=z) (z':=affixe_vec (vec O N)) (A:=O)
    (B:=M) (A':=O) (B':=N)); auto.
replace (Rinj (-1)) with (Copp oneC).
ring.
unfold oneC, Rinj in |- *.
rewrite Copp_algebrique; auto.
RReplace (-0) 0; auto.
VReplace (mult_PP (-1) (vec O M)) (vec M O).
rewrite (milieu_vecteur H8); auto.
Qed.
 
Theorem inversion_pole_origine_complexe :
 forall (k : R) (z z' : C) (M M' : PO),
 O <> M :>PO ->
 k <> 0 ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 M' = inversion O k M :>PO -> z' = Cmult (Rinj k) (Cinv (Conj z)).
intros.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H4; try clear total_order
 | intros H4; elim H4;
    [ intros H5; try clear H4 total_order; try exact H5
    | intros H5; try clear H4 total_order ] ].
rewrite (inversion_negatif_complexe (k:=k) (z:=z) (z':=z') (M:=M) (M':=M'));
 auto.
absurd (k = 0); auto.
rewrite (inversion_positif_complexe (k:=k) (z:=z) (z':=z') (M:=M) (M':=M'));
 auto.
Qed.
 
Theorem complexe_inversion_pole_origine :
 forall (k : R) (z z' : C) (M M' : PO),
 O <> M :>PO ->
 k <> 0 ->
 z = affixe_vec (vec O M) :>C ->
 z' = affixe_vec (vec O M') :>C ->
 z' = Cmult (Rinj k) (Cinv (Conj z)) -> M' = inversion O k M :>PO.
intros.
apply homothetie_inversion; auto.
apply vecteur_homothetie; auto.
apply
 (produit_reel_affixe_vecteur_OM (k:=/ Rsqr (distance O M) * k) (z:=z)
    (z':=z') (M:=M) (M':=M')); auto.
rewrite H3.
rewrite Rinj_Cmult.
assert (z <> zeroC).
apply points_distincts_non_zeroC with (1 := H); auto with geo.
assert (Conj z <> zeroC); auto with geo.
rewrite <- (module_def2 (z:=z) (M:=M)); auto with geo.
rewrite Rinj_Cinv.
rewrite <- produit_Conj_module.
rewrite Cinv_Cmult; auto.
replace (Cmult (Cmult (Cmult (Cinv z) (Cinv (Conj z))) (Rinj k)) z) with
 (Cmult (Cmult z (Cinv z)) (Cmult (Cinv (Conj z)) (Rinj k))).
2: ring.
rewrite Cinv_def; auto.
ring.
unfold Rsqr in |- *.
assert (module z <> 0); auto with geo.
auto with real.
Qed.
 
Theorem ecriture_complexe_inversion_pole_origine :
 forall (k : R) (z z' : C) (M M' : PO),
 O <> M ->
 k <> 0 ->
 z = affixe M ->
 z' = affixe M' ->
 (M' = inversion O k M <-> z' = Cmult (Rinj k) (Cinv (Conj z))).
intros; red in |- *; try split; intros.
apply
 (inversion_pole_origine_complexe (k:=k) (z:=z) (z':=z') (M:=M) (M':=M'));
 auto with geo.
apply
 (complexe_inversion_pole_origine (k:=k) (z:=z) (z':=z') (M:=M) (M':=M'));
 auto with geo.
Qed.
 
Theorem inversion_complexe :
 forall (k : R) (j z z' : C) (J M M' : PO),
 J <> M ->
 k <> 0 ->
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 M' = inversion J k M ->
 Cplus z' (Copp j) = Cmult (Rinj k) (Cinv (Conj (Cplus z (Copp j)))).
intros.
elim existence_representant_vecteur with (A := O) (B := J) (C := M); intros N;
 intros.
elim existence_representant_vecteur with (A := O) (B := J) (C := M');
 intros N'; intros.
assert (O <> N).
apply distinct_egalite_vecteur with (2 := H5); auto.
assert (vec J M' = mult_PP (/ Rsqr (distance J M) * k) (vec J M)).
apply homothetie_vecteur.
apply inversion_homothetie; auto.
generalize H8.
replace (Rsqr (distance J M)) with (Rsqr (distance O N)).
rewrite <- H6; rewrite <- H5; intros.
assert (N' = inversion O k N).
apply homothetie_inversion; auto.
apply vecteur_homothetie; auto.
rewrite (affixe_vec_AB H3 H2).
rewrite (affixe_vec_AB H3 H1).
rewrite <- H6; rewrite <- H5.
elim existence_affixe_vecteur_point with (M := N); intros z1; intros.
elim existence_affixe_vecteur_point with (M := N'); intros z2; intros.
rewrite <- H12; rewrite <- H11.
apply inversion_pole_origine_complexe with (5 := H10); auto.
unfold Rsqr in |- *.
repeat rewrite <- carre_scalaire_distance.
rewrite H5; auto.
Qed.
 
Theorem complexe_inversion :
 forall (k : R) (j z z' : C) (J M M' : PO),
 J <> M ->
 k <> 0 ->
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 Cplus z' (Copp j) = Cmult (Rinj k) (Cinv (Conj (Cplus z (Copp j)))) ->
 M' = inversion J k M.
intros.
elim existence_representant_vecteur with (A := O) (B := J) (C := M); intros N;
 intros.
elim existence_representant_vecteur with (A := O) (B := J) (C := M');
 intros N'; intros.
assert (O <> N).
apply distinct_egalite_vecteur with (2 := H5); auto.
apply homothetie_inversion; auto.
apply vecteur_homothetie.
rewrite <- H6; rewrite <- H5.
replace (Rsqr (distance J M)) with (Rsqr (distance O N)).
assert (N' = inversion O k N).
apply complexe_inversion_pole_origine with (5 := H4); auto.
rewrite H5; auto with geo.
rewrite H6; auto with geo.
apply homothetie_vecteur.
apply inversion_homothetie; auto.
unfold Rsqr in |- *.
repeat rewrite <- carre_scalaire_distance.
rewrite H5; auto.
Qed.
 
Theorem ecriture_complexe_inversion :
 forall (k : R) (j z z' : C) (J M M' : PO),
 J <> M ->
 k <> 0 ->
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 (M' = inversion J k M <->
  Cplus z' (Copp j) = Cmult (Rinj k) (Cinv (Conj (Cplus z (Copp j))))).
intros; red in |- *; try split; intros.
apply
 (inversion_complexe (k:=k) (j:=j) (z:=z) (z':=z') (J:=J) (M:=M) (M':=M'));
 auto.
apply
 (complexe_inversion (k:=k) (j:=j) (z:=z) (z':=z') (J:=J) (M:=M) (M':=M'));
 auto.
Qed.
