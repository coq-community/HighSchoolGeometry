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


Require Export similitudes_directes.
Require Export complexes_dilatations.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma isometrie_egalite_module :
 forall (A B A' B' : PO) (z z' : C),
 distance A' B' = distance A B ->
 z = affixe_vec (vec A B) ->
 z' = affixe_vec (vec A' B') -> module z' = module z.
intros A B A' B' z z'; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B); intros M;
 intros H1.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros M'; intros H2.
rewrite <- H2; rewrite <- H1; intros.
rewrite (module_def2 (z:=z) (M:=M)); auto with geo.
rewrite (module_def2 (z:=z') (M:=M')); auto with geo.
rewrite (egalite_vecteur_distance (A:=O) (B:=M') (C:=A') (D:=B'));
 auto with geo.
rewrite H; auto with geo.
Qed.
 
Lemma angle_vecteurs_arguments :
 forall (A B A' B' : PO) (z z' : C),
 A <> B ->
 A' <> B' ->
 z = affixe_vec (vec A B) ->
 z' = affixe_vec (vec A' B') ->
 cons_AV (vec A B) (vec A' B') = plus (argument z') (opp (argument z)).
intros A B A' B' z z'; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B); intros M;
 intros H1.
elim existence_representant_vecteur with (A := O) (B := A') (C := B');
 intros M'; intros H2.
rewrite <- H2; rewrite <- H1; intros.
apply angle_argument; auto with geo.
apply distinct_egalite_vecteur with (2 := H1); auto.
apply distinct_egalite_vecteur with (2 := H2); auto.
Qed.
 
Theorem complexe_rotation_centre_origine :
 forall (a : R) (z z' : C) (M M' : PO),
 z = affixe M ->
 z' = affixe M' -> z' = Cmult (cons_pol 1 a) z -> M' = rotation O a M.
intros.
cut (module z' = module z); intros.
discrimine O M.
cut (z = zeroC); intros.
replace M with M'.
rewrite <- rotation_def_centre; auto.
apply (egalite_affixe_point (z:=z') (z':=z) (M:=M') (M':=M)); auto.
rewrite H1; rewrite H4; ring.
apply (egalite_point_image (z:=z) (z':=zeroC) (M:=M) (M':=O)); auto with geo.
apply rotation_def2; auto.
rewrite <- (module_def2 (z:=z) (M:=M)); auto.
rewrite <- (module_def2 (z:=z') (M:=M')); auto.
cut (z <> zeroC); intros; [ idtac | eauto with geo ].
cut (z' <> zeroC); intros.
cut (O <> M'); intros; [ idtac | eauto with geo ].
rewrite (angle_argument (z:=z) (z':=z') (M:=M) (M':=M')); auto with geo.
rewrite H1; rewrite Cmult_argument; auto with geo.
rewrite argument_module_un.
elim existence_argument with (z := z);
 [ intros; try clear existence_argument | auto with geo ].
rewrite H7.
rewrite <- mes_opp; auto.
repeat rewrite <- add_mes_compatible.
replace (a + x + - x) with a; [ auto | ring ].
apply nonzero_module.
rewrite H2; auto with geo.
rewrite H1; rewrite Cmult_module; rewrite module_un_trivial; ring.
Qed.
 
Lemma nonzero_diff :
 forall (a b : C) (A B : PO),
 a = affixe A -> b = affixe B -> Cplus b (Copp a) <> zeroC -> A <> B.
intros.
red in |- *; intros; apply H1.
rewrite (affixe_vec_AB (a:=a) (b:=b) (A:=A) (B:=B)); auto.
rewrite affixe_vec_AB_affixes; rewrite H2; ring.
Qed.
Hint Resolve nonzero_diff: geo.
 
Theorem complexe_rotation :
 forall (a : R) (j z z' : C) (J M M' : PO),
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 Cplus z' (Copp j) = Cmult (cons_pol 1 a) (Cplus z (Copp j)) ->
 M' = rotation J a M.
intros.
cut (module (Cplus z' (Copp j)) = module (Cplus z (Copp j))); intros.
discrimine J M.
cut (Cplus z (Copp j) = zeroC); intros.
replace M with M'.
rewrite <- rotation_def_centre; auto.
apply egalite_vecteur_point with J.
apply
 (egalite_affixe_vecteur (z:=Cplus z' (Copp j)) (z':=
    Cplus z (Copp j)) (A:=J) (B:=M') (A':=J) (B':=M)); 
 auto with geo.
rewrite H2; rewrite H5; ring.
apply (egalite_point_zeroC (z:=Cplus z (Copp j)) (A:=J) (B:=M));
 auto with geo.
apply rotation_def2; auto.
rewrite <- (module_difference (a:=j) (b:=z) (A:=J) (B:=M)); auto.
rewrite <- (module_difference (a:=j) (b:=z') (A:=J) (B:=M')); auto.
cut (Cplus z (Copp j) <> zeroC); intros; [ idtac | eauto with geo ].
cut (Cplus z' (Copp j) <> zeroC); intros.
cut (J <> M'); intros.
rewrite
 (angle_vecteurs_arguments (A:=J) (B:=M) (A':=J) (B':=M')
    (z:=Cplus z (Copp j)) (z':=Cplus z' (Copp j))); 
 auto with geo.
rewrite H2; rewrite Cmult_argument; auto with geo.
rewrite argument_module_un.
elim existence_argument with (z := Cplus z (Copp j));
 [ intros; try clear existence_argument | auto ].
rewrite H8; repeat rewrite <- mes_opp.
repeat rewrite <- add_mes_compatible.
replace (a + x + - x) with a; [ auto | ring ].
eauto with geo.
apply nonzero_module.
rewrite H3; auto with geo.
rewrite H2; rewrite Cmult_module; rewrite module_un_trivial; ring.
Qed.
 
Theorem rotation_centre_origine_complexe :
 forall (a : R) (z z' : C) (M M' : PO),
 z = affixe M ->
 z' = affixe M' -> M' = rotation O a M -> z' = Cmult (cons_pol 1 a) z.
intros a z z' M M'; try assumption.
discrimine M O.
intros.
rewrite H1; rewrite H2; rewrite <- rotation_def_centre; rewrite H0;
 rewrite <- affixe_origine; ring.
intros.
cut (O <> M); intros.
elim rotation_def with (I := O) (A := M) (B := M') (a := a);
 [ intros | auto | auto ].
cut (O <> M'); intros.
cut (z <> zeroC); intros.
cut (z' <> zeroC); intros.
cut (module z' = module z); intros.
apply egalite_forme_polaire; auto with geo.
rewrite H9; rewrite Cmult_module; rewrite module_un_trivial; ring.
rewrite Cmult_argument; auto with geo.
rewrite argument_module_un; rewrite H5.
rewrite (angle_argument (z:=z) (z':=z') (M:=M) (M':=M')); auto with geo.
elim existence_argument with (z := z);
 [ intros; try clear existence_argument | auto ].
elim existence_argument with (z := z');
 [ intros; try clear existence_argument | auto ].
rewrite H10; rewrite <- mes_opp.
rewrite H11; repeat rewrite <- add_mes_compatible.
replace (x0 + - x + x) with x0; [ auto | ring ].
rewrite (module_def2 (z:=z) (M:=M)); auto.
rewrite (module_def2 (z:=z') (M:=M')); auto.
eauto with geo.
eauto with geo.
apply isometrie_distinct with (1 := H3); auto.
auto.
Qed.
 
Theorem rotation_complexe :
 forall (a : R) (j z z' : C) (J M M' : PO),
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 M' = rotation J a M ->
 Cplus z' (Copp j) = Cmult (cons_pol 1 a) (Cplus z (Copp j)).
intros a j z z' J M M'; try assumption.
discrimine M J.
intros.
rewrite H1; rewrite H3; rewrite <- rotation_def_centre; rewrite H0;
 rewrite H2; ring.
intros.
cut (J <> M); intros.
elim rotation_def with (I := J) (A := M) (B := M') (a := a);
 [ intros | auto | auto ].
cut (J <> M'); intros.
cut (Cplus z (Copp j) <> zeroC); intros.
cut (Cplus z' (Copp j) <> zeroC); intros.
cut (module (Cplus z' (Copp j)) = module (Cplus z (Copp j))); intros.
apply egalite_forme_polaire; auto with geo.
rewrite H10; rewrite Cmult_module; rewrite module_un_trivial; ring.
rewrite Cmult_argument; auto with geo.
rewrite argument_module_un; rewrite H6.
rewrite
 (angle_vecteurs_arguments (A:=J) (B:=M) (A':=J) (B':=M')
    (z:=Cplus z (Copp j)) (z':=Cplus z' (Copp j))); 
 auto with geo.
elim existence_argument with (z := Cplus z (Copp j));
 [ intros; try clear existence_argument | auto ].
elim existence_argument with (z := Cplus z' (Copp j));
 [ intros; try clear existence_argument | auto ].
rewrite H11; repeat rewrite <- mes_opp.
rewrite H12; repeat rewrite <- add_mes_compatible.
replace (x0 + - x + x) with x0; [ auto | ring ].
rewrite (module_difference (a:=j) (b:=z) (A:=J) (B:=M)); auto.
rewrite (module_difference (a:=j) (b:=z') (A:=J) (B:=M')); auto.
eauto with geo.
eauto with geo.
apply isometrie_distinct with (1 := H4); auto.
auto.
Qed.
 
Theorem similitude_complexe :
 forall (k a : R) (j z z' : C) (J M M' : PO),
 k > 0 ->
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 M' = similitude J k a M ->
 Cplus z' (Copp j) = Cmult (cons_pol k a) (Cplus z (Copp j)).
intros k a j z z' J M M' H; try assumption.
discrimine M J.
intros.
rewrite H2; rewrite H4; rewrite <- similitude_def_centre; auto; rewrite H1;
 rewrite H3; ring.
intros.
cut (J <> M); intros.
elim similitude_def with (I := J) (A := M) (B := M') (k := k) (a := a);
 [ intros | auto | auto | auto ].
cut (J <> M'); intros.
cut (Cplus z (Copp j) <> zeroC); intros.
cut (Cplus z' (Copp j) <> zeroC); intros.
cut (module (Cplus z' (Copp j)) = k * module (Cplus z (Copp j))); intros.
cut (cons_pol k a <> zeroC); intros; auto with real geo.
apply egalite_forme_polaire; auto with geo.
rewrite H11; rewrite Cmult_module; rewrite complexe_polaire_module; ring.
rewrite Cmult_argument; auto with geo.
rewrite complexe_polaire_argument; auto with real geo.
rewrite H7.
rewrite
 (angle_vecteurs_arguments (A:=J) (B:=M) (A':=J) (B':=M')
    (z:=Cplus z (Copp j)) (z':=Cplus z' (Copp j))); 
 auto with geo.
elim existence_argument with (z := Cplus z (Copp j));
 [ intros; try clear existence_argument | auto ].
elim existence_argument with (z := Cplus z' (Copp j));
 [ intros; try clear existence_argument | auto ].
rewrite H13; rewrite H14; repeat rewrite <- mes_opp;
 repeat rewrite <- add_mes_compatible.
replace (x0 + - x + x) with x0; [ auto | ring ].
rewrite (module_difference (a:=j) (b:=z) (A:=J) (B:=M)); auto.
rewrite (module_difference (a:=j) (b:=z') (A:=J) (B:=M')); auto.
eauto with geo.
eauto with geo.
apply image_sim_distinct_centre with (3 := H4); auto.
auto.
Qed.
 
Theorem complexe_similitude :
 forall (k a : R) (j z z' : C) (J M M' : PO),
 k > 0 ->
 z = affixe M ->
 z' = affixe M' ->
 j = affixe J ->
 Cplus z' (Copp j) = Cmult (cons_pol k a) (Cplus z (Copp j)) ->
 M' = similitude J k a M.
intros.
cut (module (Cplus z' (Copp j)) = k * module (Cplus z (Copp j))); intros.
discrimine J M.
cut (Cplus z (Copp j) = zeroC); intros.
replace M with M'.
rewrite <- similitude_def_centre; auto.
apply egalite_vecteur_point with J.
apply
 (egalite_affixe_vecteur (z:=Cplus z' (Copp j)) (z':=
    Cplus z (Copp j)) (A:=J) (B:=M') (A':=J) (B':=M)); 
 auto with geo.
rewrite H3; rewrite H6; ring.
apply (egalite_point_zeroC (z:=Cplus z (Copp j)) (A:=J) (B:=M));
 auto with geo.
apply similitude_def2; auto.
rewrite <- (module_difference (a:=j) (b:=z) (A:=J) (B:=M)); auto.
rewrite <- (module_difference (a:=j) (b:=z') (A:=J) (B:=M')); auto.
cut (Cplus z (Copp j) <> zeroC); intros; [ idtac | eauto with geo ].
cut (Cplus z' (Copp j) <> zeroC); intros.
cut (J <> M'); intros.
rewrite
 (angle_vecteurs_arguments (A:=J) (B:=M) (A':=J) (B':=M')
    (z:=Cplus z (Copp j)) (z':=Cplus z' (Copp j))); 
 auto with geo.
rewrite H3; rewrite Cmult_argument; auto with geo.
rewrite complexe_polaire_argument; auto with real geo.
elim existence_argument with (z := Cplus z (Copp j));
 [ intros; try clear existence_argument | auto ].
rewrite H9; repeat rewrite <- mes_opp; repeat rewrite <- add_mes_compatible.
replace (a + x + - x) with a; [ auto | ring ].
auto with real geo.
eauto with geo.
apply nonzero_module.
rewrite H4; apply Rmult_integral_contrapositive; split; auto with real geo.
rewrite H3; rewrite Cmult_module; rewrite complexe_polaire_module; ring.
Qed.