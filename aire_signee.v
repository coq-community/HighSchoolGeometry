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


Require Export trigo.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter aire : PP -> PP -> R.
 
Axiom
  def_aire_0 :
    forall A B C D : PO, A = B \/ C = D -> aire (vec A B) (vec C D) = 0.
 
Axiom
  def_aire :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    aire (vec A B) (vec C D) =
    distance A B * (distance C D * Sin (cons_AV (vec A B) (vec C D))).
 
Lemma Sin_opp :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 Sin (cons_AV (vec C D) (vec A B)) = - Sin (cons_AV (vec A B) (vec C D)).
intros.
elim (existence_representant_vecteur A C D); intros E; intros.
rewrite <- H1.
cut (A <> E); intros.
mesure A B A E.
rewrite H3.
generalize (mes_oppx (A:=A) (B:=B) (C:=A) (D:=E) (x:=x)); auto; intros.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=E) (x:=x)); auto.
rewrite <- (egalite_sin_Sin (A:=A) (B:=E) (C:=B) (x:=- x)); auto.
rewrite sin_impaire; auto.
apply distinct_egalite_vecteur with (A := C) (B := D); auto.
Qed.
 
Lemma aire_anti_symetrique :
 forall A B C D : PO, aire (vec A B) (vec C D) = - aire (vec C D) (vec A B).
intros.
elim (classic (A = B \/ C = D)); intros.
rewrite def_aire_0; auto.
rewrite def_aire_0; auto.
ring.
tauto.
cut (A <> B /\ C <> D); intros.
elim H0; intros.
rewrite def_aire; auto.
rewrite def_aire; auto.
rewrite Sin_opp; auto.
ring.
apply not_or_and; auto.
Qed.
 
Lemma aire_ABAB : forall A B : PO, aire (vec A B) (vec A B) = 0.
intros.
elim (classic (A = B)); intros.
rewrite def_aire_0; auto.
rewrite def_aire; auto.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=B) (x:=0)); auto.
rewrite sin_zero; ring.
apply angle_nul; auto.
Qed.
 
Lemma aire_AB_oppAB :
 forall A B C : PO, aire (vec A B) (mult_PP (-1) (vec A B)) = 0.
intros.
elim (existence_representant_mult_vecteur A A B (-1)); auto; intros D H.
rewrite <- H.
elim (classic (A = B)); intros.
rewrite def_aire_0; auto.
cut (A <> D); intros.
rewrite def_aire; auto.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=D) (x:=pi)); auto.
rewrite sin_pi; ring.
replace (vec A D) with (vec B A).
apply angle_plat; auto.
rewrite H; Ringvec.
apply distinct_produit_vecteur with (3 := H); auto with real.
Qed.
Hint Resolve aire_ABAB aire_AB_oppAB aire_anti_symetrique: geo.
 
Ltac deroule_representant_unitaire A B C :=
  elim (existence_representant_unitaire (A:=A) (B:=B)); auto; intros C;
   intros; elim (def_representant_unitaire2 (A:=A) (B:=B) (C:=C)); 
   auto; intros; applatit_and; cut (A <> C); intros;
   [ idtac | auto with geo ].
Hint Resolve sin_zero sin_pisurdeux sin_pi angle_nul angle_plat: geo.
 
Lemma Sin_angles_alignes :
 forall A B C : PO,
 A <> B -> A <> C -> alignes A B C -> Sin (cons_AV (vec A B) (vec A C)) = 0.
intros.
deroule_representant_unitaire A B ipattern:D.
deroule_representant_unitaire A C ipattern:E.
rewrite angles_representants_unitaires; auto.
elim alignes_representant_unitaire with (A := A) (B := B) (C := C);
 [ intros H12 | intros H12 | auto | auto | auto ].
rewrite H12; rewrite <- H7.
rewrite <- (egalite_sin_Sin (A:=A) (B:=E) (C:=E) (x:=0)); auto with geo.
rewrite H12; rewrite <- H2.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := D) (k := -1);
 [ intros F H13; try clear existence_representant_mult_vecteur; try exact H13 ].
rewrite <- H13.
rewrite <- (egalite_sin_Sin (A:=A) (B:=D) (C:=F) (x:=pi)); auto with geo.
apply distinct_produit_vecteur with (3 := H13); auto with real.
rewrite H13.
VReplace (mult_PP (-1) (vec A D)) (vec D A); auto with geo.
Qed.
 
Lemma aire_vecteur_nul_r : forall A B : PO, aire (vec A B) zero = 0.
intros.
VReplace zero (vec A A).
rewrite def_aire_0; auto.
Qed.
Hint Resolve aire_vecteur_nul_r: geo.
 
Lemma aire_vecteur_nul_l : forall A B : PO, aire zero (vec A B) = 0.
intros.
VReplace zero (vec A A).
rewrite def_aire_0; auto.
Qed.
Hint Resolve aire_vecteur_nul_l: geo.
 
Lemma aire_alignement :
 forall A B C : PO, alignes A B C -> aire (vec A B) (vec A C) = 0.
intros.
discrimine A B.
VReplace (vec B B) zero; auto with geo.
discrimine A C.
VReplace (vec C C) zero; auto with geo.
rewrite def_aire; auto.
rewrite Sin_angles_alignes; auto.
ring.
Qed.
 
Lemma aire_colinearite :
 forall (k : R) (A B C D : PO),
 vec C D = mult_PP k (vec A B) -> aire (vec A B) (vec C D) = 0.
intros.
discrimine A B.
VReplace (vec B B) zero; auto with geo.
discrimine C D.
VReplace (vec D D) zero; auto with geo.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 [ intros E H2; try clear existence_representant_mult_vecteur; try exact H2 ].
replace (vec C D) with (vec A E).
apply aire_alignement; auto.
apply colineaire_alignes with k; auto.
rewrite H; auto.
Qed.
Hint Resolve distance_refl2 egalite_vecteur_distance: geo.
 
Lemma aire_colineaire_l :
 forall (k : R) (A B C D : PO),
 aire (mult_PP k (vec A B)) (vec C D) = k * aire (vec A B) (vec C D).
intros.
discrimine A B.
VReplace (mult_PP k (vec B B)) zero; auto with geo.
VReplace (vec B B) zero; auto with geo.
rewrite aire_vecteur_nul_l; ring.
discrimine C D.
VReplace (vec D D) zero; auto with geo.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 [ intros E H2; rewrite <- H2 ].
repeat rewrite aire_vecteur_nul_r; ring.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 [ intros E H2; rewrite <- H2 ].
discrimine k 0.
replace (vec A E) with zero.
ring_simplify; auto with geo.
rewrite H2; rewrite H1; Ringvec.
cut (A <> E); intros.
elim existence_representant_vecteur with (A := A) (B := C) (C := D);
 [ intros F H4; rewrite <- H4; intros ].
cut (A <> F); intros.
deroule_representant_unitaire A B ipattern:G.
deroule_representant_unitaire A F ipattern:L.
rewrite def_aire; auto.
rewrite def_aire; auto.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H16; try clear total_order
 | intros H16; elim H16;
    [ intros H17; try clear H16 | intros H17; try clear H16; try exact H17 ] ].
rewrite (produit_negatif_representant_unitaire (k:=k) (A:=A) (B:=B) (C:=E));
 auto.
rewrite <- H11; rewrite <- H6.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := G) (k := -1);
 [ intros K H17; try clear existence_representant_mult_vecteur; try exact H17 ].
mesure A G A L.
rewrite H18; rewrite <- H17.
rewrite <- (egalite_sin_Sin (A:=A) (B:=G) (C:=L) (x:=x)); auto.
rewrite <- (egalite_sin_Sin (A:=A) (B:=K) (C:=L) (x:=pi + x)); auto.
elim pi_plus_x with (x := x);
 [ intros H19 H20; try clear pi_plus_x; try exact H20 ].
rewrite H20.
replace (distance A E) with (- k * distance A B).
ring.
symmetry  in |- *.
rewrite <- Rabs_left; auto with real.
apply colinearite_distance; auto.
apply distinct_produit_vecteur with (3 := H17); auto with real.
replace (cons_AV (vec A K) (vec A L)) with
 (plus (cons_AV (vec A K) (vec A G)) (cons_AV (vec A G) (vec A L))).
replace (vec A K) with (vec G A).
rewrite <- angle_plat; auto.
rewrite <- H18; rewrite <- add_mes_compatible; auto.
rewrite H17; Ringvec.
rewrite Chasles; auto.
apply distinct_produit_vecteur with (3 := H17); auto with real.
absurd (k = 0); auto.
rewrite <-
 (produit_positif_representant_unitaire (k:=k) (A:=A) (B:=B) (C:=E))
 ; auto.
rewrite <- H11; rewrite <- H6.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := G) (k := -1);
 [ intros K H18; try clear existence_representant_mult_vecteur ].
mesure A G A L.
replace (distance A E) with (k * distance A B).
ring.
symmetry  in |- *.
rewrite <- (Rabs_right k); auto with real.
apply colinearite_distance; auto.
apply Rgt_ge; auto.
apply distinct_egalite_vecteur with (2 := H4); auto.
apply distinct_produit_vecteur with (3 := H2); auto with real.
Qed.
 
Lemma aire_colineaire_r :
 forall (k : R) (A B C D : PO),
 aire (vec A B) (mult_PP k (vec C D)) = k * aire (vec A B) (vec C D).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := C) (C := D) (k := k);
 [ intros E H2; rewrite <- H2 ].
rewrite aire_anti_symetrique.
rewrite H2; rewrite aire_colineaire_l; auto.
rewrite aire_anti_symetrique; ring.
Qed.
Hint Resolve aire_colineaire_r aire_colineaire_l: geo.
 
Lemma aire_nulle_colineaires :
 forall A B C D : PO,
 A <> B ->
 aire (vec A B) (vec C D) = 0 -> exists k : R, vec C D = mult_PP k (vec A B).
intros.
discrimine C D.
exists 0.
Ringvec.
cut (Sin (cons_AV (vec A B) (vec C D)) = 0); intros.
deroule_representant_unitaire A B ipattern:E.
deroule_representant_unitaire C D ipattern:J.
elim existence_representant_vecteur with (A := A) (B := C) (C := J);
 [ intros F H14; intros ].
elim existence_ROND_AB with (A := A) (B := E);
 [ intros G H13 | auto with geo ].
cut
 (vec A F =
  add_PP (mult_PP (Cos (cons_AV (vec A E) (vec A F))) (vec A E))
    (mult_PP (Sin (cons_AV (vec A E) (vec A F))) (vec A G))); 
 intros.
halignes H4 ipattern:k.
assert (alignes C J D); auto with geo.
halignes H17 ipattern:k'.
cut (Sin (cons_AV (vec A E) (vec A F)) = 0); intros.
rewrite H18; rewrite <- H14; rewrite H15.
pattern (vec A E) at 2 in |- *; rewrite H16; rewrite H19.
exists (k' * (Cos (cons_AV (vec A E) (vec A F)) * k)).
Ringvec.
rewrite <- H2.
rewrite H14.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
rewrite H8; rewrite H3.
rewrite representant_unitaire_bis; auto.
rewrite representant_unitaire_bis; auto.
apply coordonnees_Cos_Sin; auto.
apply carre_scalaire_1_distance.
rewrite H14; auto.
replace (Sin (cons_AV (vec A B) (vec C D))) with
 (aire (vec A B) (vec C D) * / (distance A B * distance C D)).
rewrite H0; ring.
rewrite def_aire; auto.
field; auto with geo.
Qed.
 
Lemma aire_orthogonal_direct :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 image_angle pisurdeux = cons_AV (vec A B) (vec C D) ->
 aire (vec A B) (vec C D) = distance A B * distance C D.
intros A B C D H H0; try assumption.
elim existence_representant_vecteur with (A := A) (B := C) (C := D);
 [ intros E H2; rewrite <- H2; intros ].
rewrite def_aire; auto.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=E) (x:=pisurdeux));
 auto with geo.
replace (distance C D) with (distance A E); auto with geo.
rewrite sin_pisurdeux; ring.
apply distinct_egalite_vecteur with (2 := H2); auto with geo.
apply distinct_egalite_vecteur with (2 := H2); auto with geo.
Qed.
 
Lemma aire_orthogonal_indirect :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 image_angle (- pisurdeux) = cons_AV (vec A B) (vec C D) ->
 aire (vec A B) (vec C D) = - (distance A B * distance C D).
intros A B C D H H0; try assumption.
elim existence_representant_vecteur with (A := A) (B := C) (C := D);
 [ intros E H2; rewrite <- H2; intros ].
rewrite def_aire; auto.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=E) (x:=- pisurdeux));
 auto with geo.
replace (distance C D) with (distance A E); auto with geo.
rewrite sin_impaire; rewrite sin_pisurdeux; ring.
apply distinct_egalite_vecteur with (2 := H2); auto with geo.
apply distinct_egalite_vecteur with (2 := H2); auto with geo.
Qed.
 
Lemma aire_orthogonal :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) ->
 Rabs (aire (vec A B) (vec C D)) = distance A B * distance C D.
intros.
discrimine A B.
VReplace (vec B B) zero; auto with geo.
rewrite aire_vecteur_nul_l; rewrite Rabs_R0.
replace (distance B B) with 0; [ring|idtac].
symmetry  in |- *; auto with geo.
discrimine C D.
VReplace (vec D D) zero; auto with geo.
rewrite aire_vecteur_nul_r; rewrite Rabs_R0.
replace (distance D D) with 0; [ring|idtac].
symmetry  in |- *; auto with geo.
elim orthogonal_pisurdeux_or with (A := A) (B := B) (C := C) (D := D);
 [ intros H2; try clear orthogonal_pisurdeux_or
 | intros H2; try clear orthogonal_pisurdeux_or; try exact H2
 | auto
 | auto
 | auto ].
rewrite aire_orthogonal_direct; auto.
rewrite Rabs_mult; rewrite Rabs_right; auto with geo.
rewrite Rabs_right; auto with geo.
rewrite aire_orthogonal_indirect; auto.
rewrite Rabs_Ropp; rewrite Rabs_mult; rewrite Rabs_right; auto with geo.
rewrite Rabs_right; auto with geo.
Qed.
 
Axiom
  aire_distrib_l :
    forall A B C D E F : PO,
    aire (vec A B) (add_PP (vec C D) (vec E F)) =
    aire (vec A B) (vec C D) + aire (vec A B) (vec E F).
 
Lemma aire_distrib_r :
 forall A B C D E F : PO,
 aire (add_PP (vec A B) (vec C D)) (vec E F) =
 aire (vec A B) (vec E F) + aire (vec C D) (vec E F).
intros.
replace (aire (vec A B) (vec E F) + aire (vec C D) (vec E F)) with
 (- (aire (vec E F) (vec A B) + aire (vec E F) (vec C D))).
rewrite <- aire_distrib_l.
elim
 existence_representant_som_vecteur with (A := A) (B := B) (C := C) (D := D);
 [ intros G H2; rewrite <- H2 ].
auto with geo.
rewrite aire_anti_symetrique.
rewrite (aire_anti_symetrique E F C D); ring.
Qed.
 
Lemma aire_ordre_cycle :
 forall A B C : PO, aire (vec B C) (vec B A) = aire (vec A B) (vec A C).
intros.
VReplace (vec B C) (add_PP (vec B A) (vec A C)).
rewrite aire_distrib_r; rewrite aire_ABAB; ring_simplify.
VReplace (vec B A) (mult_PP (-1) (vec A B)).
rewrite aire_colineaire_r; rewrite aire_anti_symetrique; ring.
Qed.
 
Lemma aire_ordre_cycle2 :
 forall A B C : PO, aire (vec C A) (vec C B) = aire (vec A B) (vec A C).
intros.
rewrite aire_ordre_cycle; rewrite aire_ordre_cycle; auto.
Qed.
 
Lemma produit_longueur_absolu_Sin :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 distance A B * (distance A C * Rabs (Sin (cons_AV (vec A B) (vec A C)))) =
 distance B C * (distance B A * Rabs (Sin (cons_AV (vec B C) (vec B A)))).
intros.
replace
 (distance A B * (distance A C * Rabs (Sin (cons_AV (vec A B) (vec A C)))))
 with (Rabs (aire (vec A B) (vec A C))).
rewrite <- aire_ordre_cycle; auto.
rewrite def_aire; auto.
repeat rewrite Rabs_mult.
rewrite Rabs_right; auto with geo.
rewrite Rabs_right; auto with geo.
rewrite def_aire; auto.
repeat rewrite Rabs_mult.
rewrite Rabs_right; auto with geo.
rewrite Rabs_right; auto with geo.
Qed.
 
Lemma produit_longueur_absolu_Sin2 :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 distance A B * (distance A C * Rabs (Sin (cons_AV (vec A B) (vec A C)))) =
 distance C A * (distance C B * Rabs (Sin (cons_AV (vec C A) (vec C B)))).
intros.
replace
 (distance A B * (distance A C * Rabs (Sin (cons_AV (vec A B) (vec A C)))))
 with (Rabs (aire (vec A B) (vec A C))).
rewrite <- aire_ordre_cycle2; auto.
rewrite def_aire; auto.
repeat rewrite Rabs_mult.
rewrite Rabs_right; auto with geo.
rewrite Rabs_right; auto with geo.
rewrite def_aire; auto.
repeat rewrite Rabs_mult.
rewrite Rabs_right; auto with geo.
rewrite Rabs_right; auto with geo.
Qed.
Hint Resolve distance_sym: geo.
 
Theorem sinA_sur_a :
 forall (a b c sin_A sin_B sin_C : R) (A B C : PO),
 triangle A B C ->
 a = distance B C ->
 b = distance A C ->
 c = distance A B ->
 sin_A = Rabs (Sin (cons_AV (vec A B) (vec A C))) ->
 sin_B = Rabs (Sin (cons_AV (vec B C) (vec B A))) ->
 sin_C = Rabs (Sin (cons_AV (vec C A) (vec C B))) ->
 sin_A / a = sin_B / b /\ sin_A / a = sin_C / c.
intros.
rewrite H0; rewrite H1; rewrite H2; rewrite H5; rewrite H4; rewrite H3.
deroule_triangle A B C.
split; [ try assumption | idtac ].
replace (Rabs (Sin (cons_AV (vec A B) (vec A C)))) with
 (/ distance A B * / distance A C *
  (distance B C * (distance B A * Rabs (Sin (cons_AV (vec B C) (vec B A)))))).
replace (distance A B) with (distance B A); auto with geo.
field; repeat split; auto with geo.
rewrite <- produit_longueur_absolu_Sin; auto.
field; split; auto with geo.
replace (Rabs (Sin (cons_AV (vec A B) (vec A C)))) with
 (/ distance A B * / distance A C *
  (distance C A * (distance C B * Rabs (Sin (cons_AV (vec C A) (vec C B)))))).
replace (distance A C) with (distance C A); auto with geo.
replace (distance B C) with (distance C B); auto with geo.
field; repeat split; auto with geo.
rewrite <- produit_longueur_absolu_Sin2; auto.
field; split; auto with geo.
Qed.
 
Definition aire_triangle (A B C : PO) :=
  / 2 * Rabs (aire (vec A B) (vec A C)).
 
Lemma aire_triangle_ordre_permute :
 forall A B C : PO, aire_triangle A B C = aire_triangle A C B.
unfold aire_triangle in |- *; intros.
rewrite aire_anti_symetrique; rewrite Rabs_Ropp; auto.
Qed.
 
Lemma aire_triangle_ordre_cycle :
 forall A B C : PO, aire_triangle A B C = aire_triangle B C A.
unfold aire_triangle in |- *; intros.
rewrite <- aire_ordre_cycle; auto.
Qed.
 
Theorem sinA_sur_a_aire :
 forall (a b c sin_A sin_B sin_C S : R) (A B C : PO),
 triangle A B C ->
 a = distance B C ->
 b = distance A C ->
 c = distance A B ->
 S = aire_triangle A B C ->
 sin_A = Rabs (Sin (cons_AV (vec A B) (vec A C))) ->
 sin_B = Rabs (Sin (cons_AV (vec B C) (vec B A))) ->
 sin_C = Rabs (Sin (cons_AV (vec C A) (vec C B))) ->
 (sin_A / a = sin_B / b /\ sin_A / a = sin_C / c) /\
 sin_A / a = 2 * S / (a * (b * c)).
unfold aire_triangle in |- *;
 intros a b c d e f g A B C H H0 H1 H2 H3 H4 H5 H6.
split; [ try assumption | idtac ].
apply sinA_sur_a with (1 := H); auto.
deroule_triangle A B C.
rewrite H0; rewrite H1; rewrite H2; rewrite H4; rewrite H3.
rewrite def_aire; auto.
rewrite Rabs_mult.
rewrite Rabs_mult.
rewrite (Rabs_right (distance A B)); auto with geo.
rewrite (Rabs_right (distance A C)); auto with geo.
rewrite <- H4; rewrite <- H2; rewrite <- H1; rewrite <- H0.
field.
rewrite H0; rewrite H1; rewrite H2.
repeat split; auto with geo.
Qed.
Require Export projection_orthogonale.
 
Lemma aire_avec_projete :
 forall A B C H : PO,
 A <> B ->
 H = projete_orthogonal A B C ->
 aire (vec A B) (vec A C) = aire (vec A B) (vec H C).
intros.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
VReplace (vec A C) (add_PP (vec A H) (vec H C)).
repeat rewrite aire_distrib_l.
rewrite aire_alignement; auto.
ring.
Qed.
 
Lemma projete_Sinus :
 forall A B C H : PO,
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 distance H C = distance A C * Rabs (Sin (cons_AV (vec A B) (vec A C))).
intros.
apply Rmult_eq_reg_l with (distance A B); auto with geo.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
rewrite <- aire_orthogonal; auto.
rewrite <- aire_avec_projete; auto.
rewrite def_aire; auto.
rewrite Rabs_mult; rewrite Rabs_right; auto with geo.
rewrite Rabs_mult; rewrite Rabs_right; auto with geo.
Qed.
 
Lemma projete_sinus :
 forall (x : R) (A B C H : PO),
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 image_angle x = cons_AV (vec A B) (vec A C) ->
 distance H C = distance A C * Rabs (sin x).
intros.
rewrite (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=x)); auto.
rewrite (projete_Sinus (A:=A) (B:=B) (C:=C) (H:=H)); auto.
Qed.
 
Lemma aire_triangle_projete :
 forall A B C H : PO,
 A <> B ->
 H = projete_orthogonal A B C ->
 aire_triangle A B C = / 2 * (distance A B * distance H C).
unfold aire_triangle in |- *; intros.
discrimine A C.
assert (H = A).
rewrite <- H2 in H1.
apply projete_axe with (2 := H1); auto with geo.
assert (H = C).
rewrite H3; auto.
assert (distance H C = 0); auto with geo.
rewrite H5.
rewrite def_aire_0.
rewrite Rabs_right; auto with real.
right; auto.
rewrite def_aire; auto.
rewrite (projete_Sinus (A:=A) (B:=B) (C:=C) (H:=H)); auto.
rewrite Rabs_mult.
rewrite Rabs_mult.
rewrite (Rabs_right (distance A B)); auto with geo.
rewrite (Rabs_right (distance A C)); auto with geo.
Qed.
