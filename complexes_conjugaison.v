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


Require Export complexes_dilatations.
Require Export reflexion_plane.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter Conj : C -> C.
 
Axiom
  Conj_def :
    forall (z : C) (x y : R), z = cons_cart x y -> Conj z = cons_cart x (- y).
 
Lemma Conj_algebrique :
 forall x y : R, Conj (cons_cart x y) = cons_cart x (- y).
intros.
rewrite (Conj_def (z:=cons_cart x y) (x:=x) (y:=y)); auto.
Qed.
Hint Resolve Conj_algebrique: geo.
 
Lemma Conj_Conj : forall z : C, Conj (Conj z) = z.
intros.
elim existence_parties_relles_imaginaires with (z := z); intros x H; elim H;
 intros y H0; try clear H; try exact H0.
rewrite H0.
repeat rewrite Conj_algebrique.
replace (- - y) with y; [ auto | ring ].
Qed.
 
Lemma Conj_somme :
 forall z1 z2 : C, Conj (Cplus z1 z2) = Cplus (Conj z1) (Conj z2).
intros.
elim existence_parties_relles_imaginaires with (z := z1); intros x1 H; elim H;
 intros y1 H0; try clear H; try exact H0.
elim existence_parties_relles_imaginaires with (z := z2); intros x2 H; elim H;
 intros y2 H1; try clear H; try exact H1.
rewrite H1; rewrite H0.
rewrite Cplus_algebrique.
repeat rewrite Conj_algebrique.
rewrite Cplus_algebrique.
replace (- (y1 + y2)) with (- y1 + - y2); [ auto | ring ].
Qed.
 
Lemma Conj_produit :
 forall z1 z2 : C, Conj (Cmult z1 z2) = Cmult (Conj z1) (Conj z2).
intros.
elim existence_parties_relles_imaginaires with (z := z1); intros x1 H; elim H;
 intros y1 H0; try clear H; try exact H0.
elim existence_parties_relles_imaginaires with (z := z2); intros x2 H; elim H;
 intros y2 H1; try clear H; try exact H1.
rewrite H1; rewrite H0.
rewrite Cmult_algebrique.
repeat rewrite Conj_algebrique.
rewrite Cmult_algebrique.
replace (- y1 * - y2) with (y1 * y2); [ idtac | ring ].
replace (- y1 * x2 + x1 * - y2) with (- (y1 * x2 + x1 * y2)); [ auto | ring ].
Qed.
 
Lemma Conj_zeroC : Conj zeroC = zeroC.
unfold zeroC in |- *.
repeat rewrite Conj_algebrique.
replace (-0) with 0; [ auto | ring ].
Qed.
 
Lemma Conj_oneC : Conj oneC = oneC.
unfold oneC in |- *.
repeat rewrite Conj_algebrique.
replace (-0) with 0; [ auto | ring ].
Qed.
 
Lemma Conj_reel : forall x : R, Conj (Rinj x) = Rinj x.
unfold Rinj in |- *; intros.
repeat rewrite Conj_algebrique.
replace (-0) with 0; [ auto | ring ].
Qed.
Hint Resolve Conj_zeroC Conj_oneC Conj_reel: geo.
 
Lemma Conj_i : Conj i = Copp i.
unfold i in |- *.
repeat rewrite Conj_algebrique; repeat rewrite Copp_algebrique.
replace (-0) with 0; [ auto | ring ].
Qed.
 
Lemma non_zero_Conj : forall z : C, z <> zeroC -> Conj z <> zeroC.
intros.
red in |- *; intros; apply H.
rewrite <- (Conj_Conj z).
rewrite H0; auto with geo.
Qed.
Hint Resolve non_zero_Conj Conj_produit Conj_somme: geo.
 
Lemma Conj_Cinv : forall z : C, z <> zeroC -> Conj (Cinv z) = Cinv (Conj z).
intros.
cut (Cmult z (Cinv z) = oneC); (intros; auto with geo).
cut (Cmult (Conj z) (Conj (Cinv z)) = oneC); intros.
cut (Cinv (Conj z) = Conj (Cinv z)); intros.
2: apply Cinv_def2; auto with geo.
rewrite <- H2; auto with geo.
rewrite <- Conj_produit; rewrite H0; auto with geo.
Qed.
Hint Resolve Conj_Cinv: geo.
 
Lemma Conj_Cdiv :
 forall z z' : C, z' <> zeroC -> Conj (Cdiv z z') = Cdiv (Conj z) (Conj z').
intros.
rewrite Cdiv_def; auto; rewrite Conj_produit; rewrite Conj_Cinv; auto.
rewrite <- Cdiv_def; auto with geo.
Qed.
 
Lemma module_Conj : forall z : C, module (Conj z) = module z.
intros.
elim existence_parties_relles_imaginaires with (z := z); intros x H; elim H;
 intros y H0; try clear H; try exact H0.
cut (Conj z = cons_cart x (- y)); intros.
rewrite (passage_algebrique_module H); rewrite (passage_algebrique_module H0).
replace (Rsqr (- y)) with (Rsqr y); [ auto | unfold Rsqr in |- *; ring ].
apply Conj_def; auto.
Qed.
 
Lemma argument_Conj :
 forall (z : C) (a : R),
 z <> zeroC ->
 argument z = image_angle a -> argument (Conj z) = image_angle (- a).
intros.
elim existence_parties_relles_imaginaires with (z := z); intros x H1; elim H1;
 intros y H2; try clear H1; try exact H2.
cut (Conj z = cons_cart x (- y)); intros.
2: apply Conj_def; auto.
elim existence_module with (z := z); intros r H3; try clear existence_module;
 try exact H3.
elim
 passage_algebrique_argument
  with (z := z) (r := r) (x := x) (y := y) (a := a);
 [ try intros; try exact H5 | auto with geo | auto with geo | auto with geo ].
cut (module (Conj z) = r); intros.
elim existence_argument with (z := Conj z);
 [ intros b H7; try clear existence_argument; try exact H7 | auto with geo ].
elim
 passage_algebrique_argument
  with (z := Conj z) (r := r) (x := x) (y := - y) (a := b);
 [ try intros | auto with geo | auto with geo | auto with geo ].
rewrite H7.
apply egalite_angle_trigo.
rewrite H9; rewrite sin_impaire; rewrite H5; ring.
rewrite H8; rewrite cos_paire; rewrite H4; ring.
rewrite module_Conj; auto.
Qed.
 
Lemma forme_polaire_Conj :
 forall (z : C) (r a : R),
 z <> zeroC -> z = cons_pol r a -> Conj z = cons_pol r (- a).
intros.
apply forme_polaire_def; auto with geo.
rewrite module_Conj; auto.
eauto with geo.
apply argument_Conj; auto with geo.
eauto with geo.
Qed.
 
Lemma argument_Conj2 :
 forall z : C, z <> zeroC -> argument (Conj z) = opp (argument z).
intros.
elim existence_argument with (z := z);
 [ intros a H7; try clear existence_argument; try exact H7 | auto with geo ].
rewrite (argument_Conj (z:=z) (a:=a)); auto with geo.
rewrite H7; auto with geo.
Qed.
 
Theorem reflexion_conjugaison :
 forall (z z' : C) (M M' : PO),
 z = affixe M -> z' = affixe M' -> M' = reflexion O I M -> z' = Conj z.
intros z z' M M' H H0; try assumption.
discrimine O M.
cut (M <> I).
intros H20.
rewrite <- reflexion_axe; auto with geo.
cut (z = zeroC); intros.
rewrite H0; rewrite H3; rewrite <- H1; rewrite H2; auto.
symmetry  in |- *; rewrite <- affixe_origine; auto with geo.
rewrite H; rewrite <- H1; auto with geo.
rewrite <- H1; auto with geo.
discrimine I M.
rewrite <- reflexion_axe; auto with geo.
cut (z = oneC); intros.
rewrite H0; rewrite H4; rewrite <- H; rewrite H3; auto with geo.
unfold oneC in |- *.
apply cart_point_complexe with I.
Ringvec.
rewrite H; rewrite <- H2; auto.
intros.
cut (distance O M = distance O M'); intros.
2: apply (reflexion_isometrie (A:=O) (B:=I)); auto with geo.
cut (cons_AV (vec O I) (vec O M') = opp (cons_AV (vec O I) (vec O M)));
 intros.
2: apply (reflexion_anti_deplacement (A:=O) (B:=I)); auto with geo.
cut (O <> M'); intros.
cut (z <> zeroC); intros.
cut (z' <> zeroC); intros.
apply egalite_forme_polaire; auto with geo.
rewrite module_Conj.
rewrite (module_def2 H); rewrite (module_def2 H0); auto.
rewrite argument_Conj2; auto.
rewrite (argument_def2 (M:=M) (z:=z)); auto with geo.
rewrite (argument_def2 (M:=M') (z:=z')); auto with geo.
eauto with geo.
eauto with geo.
apply isometrie_distinct with (2 := H4); auto with geo.
Qed.
 
Lemma composantes_projete_orthogonal :
 forall (a b : R) (M H : PO),
 H = projete_orthogonal O I M ->
 vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) ->
 vec O H = mult_PP a (vec O I).
intros.
elim def_projete_orthogonal2 with (A := O) (B := I) (C := M) (H := H);
 [ intros | auto with geo | auto ].
halignes H2 ipattern:k.
absurd (O = I); auto with geo.
cut (vec H M = add_PP (mult_PP (a + - k) (vec O I)) (mult_PP b (vec O J)));
 intros.
cut (scalaire (vec O I) (vec H M) = a + - k); intros.
replace a with k; auto.
replace a with (k + (a + - k)); [ idtac | ring ].
cut (scalaire (vec O I) (vec H M) = 0); intros; auto with geo.
rewrite <- H6; rewrite H7; ring.
elim existence_representant_vecteur with (A := O) (B := H) (C := M);
 intros D H6; try clear existence_representant_vecteur; 
 rewrite <- H6.
rewrite
 (scalaire_coordonnees (O:=O) (I:=I) (J:=J) (M:=I) (N:=D) (x:=1) (y:=0)
    (x':=a + - k) (y':=b)); auto with geo.
ring.
Ringvec.
rewrite H6; auto with geo.
replace (vec H M) with (add_PP (vec O M) (mult_PP (-1) (vec O H)));
 [ idtac | Ringvec ].
rewrite H1; rewrite H4; Ringvec.
Qed.
 
Lemma affixe_projete_orthogonal :
 forall (z : C) (a b : R) (M H : PO),
 H = projete_orthogonal O I M ->
 z = affixe M -> z = cons_cart a b -> Rinj a = affixe H.
unfold Rinj in |- *; intros.
cut (vec O H = mult_PP a (vec O I)); intros.
symmetry  in |- *.
apply (cart_point_complexe (z:=affixe H) (a:=a) (b:=0) (M:=H)); auto.
rewrite H3; Ringvec.
apply (composantes_projete_orthogonal (a:=a) (b:=b) (M:=M) (H:=H)); auto.
eauto with geo.
Qed.
 
Theorem conjugaison_reflexion :
 forall (z : C) (M M' : PO),
 z = affixe M -> Conj z = affixe M' -> M' = reflexion O I M.
intros z M M'; try assumption.
discrimine O M.
cut (M <> I); intros.
rewrite <- reflexion_axe; auto with geo.
cut (z = zeroC); intros.
apply egalite_affixe_point with (1 := H2) (2 := H1); auto.
rewrite H3; auto with geo.
rewrite H1; rewrite <- H; auto with geo.
rewrite <- H; auto with geo.
elim (classic (alignes O I M)); intros.
rewrite <- reflexion_axe; auto with geo.
apply egalite_affixe_point with (1 := H2) (2 := H1); auto.
halignes H0 ipattern:k.
absurd (O = I); auto with geo.
cut (z = cons_cart k 0); intros.
2: apply cart_point_complexe with M; auto.
rewrite H4; rewrite Conj_algebrique.
replace (-0) with 0; [ auto | ring ].
rewrite H3; Ringvec.
elim existence_projete_orthogonal with (A := O) (B := I) (C := M);
 [ intros N H4; try clear existence_projete_orthogonal; try exact H4
 | auto with geo ].
apply reflexion_def2 with N; auto with geo.
elim existence_parties_relles_imaginaires with (z := z); intros a H6; elim H6;
 intros b H7; try clear H6 existence_parties_relles_imaginaires; 
 try exact H7.
cut (Rinj a = affixe N); intros.
apply
 produit_reel_affixe_vecteur
  with (z := Cplus (Rinj a) (Copp z)) (z' := Cplus (Conj z) (Copp z));
 auto with geo.
unfold Rinj in |- *.
rewrite H7; rewrite Conj_algebrique.
rewrite Copp_algebrique; repeat rewrite Cplus_algebrique.
rewrite Cmult_algebrique.
replace (2 * (a + - a) + - (0 * (0 + - b))) with (a + - a); [ auto | ring ].
replace (0 * (a + - a) + 2 * (0 + - b)) with (- b + - b); [ auto | ring ].
apply (affixe_projete_orthogonal (z:=z) (a:=a) (b:=b) (M:=M) (H:=N)); auto.
Qed.