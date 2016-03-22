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


Require Export homothetie_plane.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter similitude : PO -> R -> R -> PO -> PO.
 
Axiom
  similitude_def :
    forall (I A B : PO) (k a : R),
    k > 0 ->
    I <> A ->
    B = similitude I k a A ->
    distance I B = k * distance I A /\
    image_angle a = cons_AV (vec I A) (vec I B).
 
Axiom
  similitude_def_centre :
    forall (I : PO) (k a : R), k > 0 -> I = similitude I k a I.
 
Axiom
  similitude_def2 :
    forall (I A B : PO) (k a : R),
    k > 0 ->
    I <> A ->
    distance I B = k * distance I A ->
    image_angle a = cons_AV (vec I A) (vec I B) -> B = similitude I k a A.
 
Lemma composee_rotation_homothetie_pos :
 forall (I M M' M1 : PO) (k a : R),
 k > 0 ->
 M1 = rotation I a M -> M' = homothetie k I M1 -> M' = similitude I k a M.
intros I M M' M1 k a H; try assumption.
discrimine I M.
rewrite <- similitude_def_centre; auto; rewrite <- rotation_def_centre;
 intros.
rewrite H2; rewrite H1; rewrite <- homothetie_centre; auto.
intros.
elim rotation_def with (I := I) (A := M) (B := M1) (a := a);
 [ intros | auto | auto ].
cut (distance I M' = Rabs k * distance I M1); intros.
2: apply distance_homothetie with I; auto with geo.
apply similitude_def2; auto.
rewrite H5; rewrite H3; rewrite Rabs_right; auto.
fourier.
rewrite H4; auto.
cut (vec I M' = mult_PP k (vec I M1)); intros.
symmetry  in |- *;
 rewrite
  (angle_produit_positif_r (k:=k) (A:=I) (B:=M1) (C:=M') (D:=I) (E:=M))
  ; auto.
apply image_distinct_centre with (2 := H1); auto.
apply homothetie_vecteur; auto.
Qed.
 
Lemma composee_homothetie_pos_rotation :
 forall (I M M' M1 : PO) (k a : R),
 k > 0 ->
 M1 = homothetie k I M -> M' = rotation I a M1 -> M' = similitude I k a M.
intros I M M' M1 k a H; try assumption.
discrimine I M.
rewrite <- similitude_def_centre; auto; rewrite <- homothetie_centre; intros.
rewrite H2; rewrite H1; rewrite <- rotation_def_centre; auto.
intros.
cut (vec I M1 = mult_PP k (vec I M)); intros.
cut (distance I M1 = Rabs k * distance I M); intros.
2: apply distance_homothetie with I; auto with geo.
cut (I <> M1); intros.
cut (I <> M'); intros.
elim rotation_def with (I := I) (A := M1) (B := M') (a := a);
 [ intros | auto | auto ].
apply similitude_def2; auto.
rewrite <- H7; rewrite H4; rewrite Rabs_right; auto.
fourier.
rewrite H8.
apply permute_angles; auto.
rewrite (angle_produit_positif_r (k:=k) (A:=I) (B:=M) (C:=M1) (D:=I) (E:=M'));
 auto.
apply image_distinct_centre with (2 := H2); auto with geo.
apply distinct_produit_vecteur with (3 := H3); auto.
auto with real.
apply homothetie_vecteur; auto.
Qed.
 
Lemma existence_similitude_Ika :
 forall (I M : PO) (k a : R),
 k > 0 -> exists M' : PO, M' = similitude I k a M.
intros.
elim existence_rotation_Ia with (I := I) (M := M) (a := a); intros M1; intros.
elim existence_homothetique with (k := k) (I := I) (A := M1); intros M' H1;
 try clear existence_homothetique; try exact H1.
exists M'.
apply composee_rotation_homothetie_pos with M1; auto.
Qed.
 
Lemma similitude_rapport_un :
 forall (I A : PO) (a : R), rotation I a A = similitude I 1 a A.
intros.
discrimine I A.
rewrite <- rotation_def_centre; rewrite <- similitude_def_centre; auto.
fourier.
elim existence_rotation_Ia with (I := I) (M := A) (a := a); intros B; intros.
cut (B = homothetie 1 I B); intros.
2: apply homothetie_identite.
rewrite <- H0.
apply composee_rotation_homothetie_pos with B; auto.
fourier.
Qed.
 
Lemma similitude_angle_nul :
 forall (I A : PO) (k : R), k > 0 -> homothetie k I A = similitude I k 0 A.
intros.
discrimine I A.
rewrite <- homothetie_centre; rewrite <- similitude_def_centre; auto.
cut (A = rotation I 0 A); intros.
2: apply rotation_angle_nul.
elim existence_homothetique with (k := k) (I := I) (A := A); intros M';
 intros.
rewrite <- H2.
apply composee_rotation_homothetie_pos with A; auto.
Qed.
 
Lemma similitude_identite : forall I A : PO, A = similitude I 1 0 A.
intros.
rewrite <- similitude_rapport_un.
rewrite <- rotation_angle_nul; auto.
Qed.
 
Lemma image_sim_distinct_centre :
 forall (I A B : PO) (k a : R),
 I <> A -> k > 0 -> B = similitude I k a A -> I <> B.
intros.
elim similitude_def with (I := I) (A := A) (B := B) (k := k) (a := a);
 [ intros | auto | auto | auto ].
apply dist_non_nulle.
rewrite H2.
apply prod_neq_R0; auto with geo.
auto with real.
Qed.
 
Lemma similitude_decomposition :
 forall (I M M' : PO) (k a : R),
 k > 0 ->
 M' = similitude I k a M ->
 exists M1 : PO, M1 = rotation I a M /\ M' = homothetie k I M1.
intros.
elim existence_rotation_Ia with (I := I) (M := M) (a := a); intros M1; intros.
exists M1.
split; [ try assumption | idtac ].
discrimine I M.
rewrite <- H2 in H1; rewrite <- H2 in H0.
rewrite <- similitude_def_centre in H0; auto;
 rewrite <- rotation_def_centre in H1.
rewrite <- H2; rewrite H0; rewrite H1; auto with geo.
cut (I <> M1); intros.
cut (I <> M'); intros.
apply vecteur_homothetie.
elim similitude_def with (I := I) (A := M) (B := M') (k := k) (a := a);
 [ intros | auto | auto | auto ].
elim rotation_def with (I := I) (A := M) (B := M1) (a := a);
 [ intros | auto | auto ].
apply alignes_distance_positif_colineaire; auto.
replace (cons_AV (vec I M1) (vec I M')) with
 (plus (cons_AV (vec I M) (vec I M')) (opp (cons_AV (vec I M) (vec I M1)))).
rewrite def_opp; auto.
rewrite <- (mes_oppx (A:=I) (B:=M) (C:=I) (D:=M1) (x:=a)); auto.
rewrite <- H6.
repeat rewrite <- add_mes_compatible.
replace (a + - a) with 0; auto.
ring.
apply Chasles_diff; auto.
rewrite <- H7; auto.
apply image_sim_distinct_centre with (3 := H0); auto.
apply image_distinct_centre with (2 := H1); auto.
Qed.
 
Lemma rotation_homothetie_pos_I_commutent :
 forall (I M M1 M2 : PO) (k a : R),
 k > 0 ->
 M1 = homothetie k I M ->
 M2 = rotation I a M -> homothetie k I M2 = rotation I a M1.
intros.
elim existence_rotation_Ia with (I := I) (M := M1) (a := a); intros N; intros.
elim existence_homothetique with (k := k) (I := I) (A := M2); intros N';
 intros.
rewrite <- H3; rewrite <- H2.
rewrite
 (composee_rotation_homothetie_pos (I:=I) (M:=M) (M':=N') (M1:=M2) (k:=k)
    (a:=a)); auto.
rewrite
 (composee_homothetie_pos_rotation (I:=I) (M:=M) (M':=N) (M1:=M1) (k:=k)
    (a:=a)); auto.
Qed.
 
Lemma similitudes_meme_centre_commutent :
 forall (I M M1 M2 : PO) (k m a b : R),
 k > 0 ->
 m > 0 ->
 M1 = similitude I k a M ->
 M2 = similitude I m b M -> similitude I k a M2 = similitude I m b M1.
intros I M M1 M2 k m a b H H0; try assumption.
discrimine I M.
repeat (rewrite <- similitude_def_centre; auto).
intros H2 H3; try assumption.
rewrite H2; rewrite H3.
repeat (rewrite <- similitude_def_centre; auto).
intros H2 H3; try assumption.
elim existence_similitude_Ika with (I := I) (M := M1) (k := m) (a := b);
 [ intros N H4 | auto ].
elim existence_similitude_Ika with (I := I) (M := M2) (k := k) (a := a);
 [ intros M' H5 | auto ].
rewrite <- H5.
cut (I <> M1); intros.
2: apply image_sim_distinct_centre with (3 := H2); auto.
cut (I <> M2); intros.
2: apply image_sim_distinct_centre with (3 := H3); auto.
cut (I <> M'); intros.
2: apply image_sim_distinct_centre with (3 := H5); auto.
cut (I <> N); intros.
2: apply image_sim_distinct_centre with (3 := H4); auto.
elim similitude_def with (I := I) (A := M2) (B := M') (k := k) (a := a);
 [ intros | auto | auto | auto ].
elim similitude_def with (I := I) (A := M1) (B := N) (k := m) (a := b);
 [ intros | auto | auto | auto ].
elim similitude_def with (I := I) (A := M) (B := M2) (k := m) (a := b);
 [ intros | auto | auto | auto ].
elim similitude_def with (I := I) (A := M) (B := M1) (k := k) (a := a);
 [ intros | auto | auto | auto ].
apply similitude_def2; auto.
rewrite H16; rewrite H10; rewrite H14; ring.
replace (cons_AV (vec I M1) (vec I M')) with
 (plus
    (plus (cons_AV (vec I M) (vec I M2)) (opp (cons_AV (vec I M) (vec I M1))))
    (cons_AV (vec I M2) (vec I M'))).
rewrite def_opp; auto.
rewrite <- (mes_oppx (A:=I) (B:=M) (C:=I) (D:=M1) (x:=a)); auto.
rewrite <- H15; rewrite <- H11.
repeat rewrite <- add_mes_compatible.
replace (b + - a + a) with b; auto.
ring.
rewrite Chasles_diff; auto.
rewrite Chasles; auto.
Qed.
 
Lemma homothetie_neg :
 forall (I M M' : PO) (k : R),
 k < 0 -> M' = homothetie k I M -> M' = similitude I (- k) pi M.
intros I M M' k H; try assumption.
discrimine I M.
rewrite <- homothetie_centre.
rewrite <- similitude_def_centre; auto.
fourier.
intros.
cut (vec I M' = mult_PP k (vec I M)); intros.
cut (distance I M' = Rabs k * distance I M); intros.
2: apply distance_homothetie with I; auto with geo.
2: apply homothetie_vecteur; auto.
cut (I <> M'); intros.
apply similitude_def2; auto.
fourier.
rewrite <- Rabs_left; auto.
rewrite (angle_produit_negatif_r (k:=k) (A:=I) (B:=M) (C:=M') (D:=I) (E:=M));
 auto.
rewrite <- angle_nul; auto.
repeat rewrite <- add_mes_compatible.
replace (0 + pi) with pi; auto.
ring.
apply distinct_produit_vecteur with (3 := H2); auto.
auto with real.
Qed.
 
Lemma homothetie_neg2 :
 forall (I M : PO) (k : R),
 k < 0 -> homothetie k I M = similitude I (- k) pi M.
intros.
elim existence_homothetique with (k := k) (I := I) (A := M); intros M';
 intros.
rewrite <- H0.
apply homothetie_neg; auto.
Qed.
 
Lemma rotation_homothetie_I_commutent :
 forall (I M M1 M2 : PO) (k a : R),
 k <> 0 ->
 M1 = homothetie k I M ->
 M2 = rotation I a M -> homothetie k I M2 = rotation I a M1.
intros I M M1 M2 k a H; try assumption.
repeat rewrite similitude_rapport_un.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H4; try clear total_order
 | intros H4;
    (elim H4;
      [ intros H5; try clear H4 total_order
      | intros H5; try clear H4 total_order; try exact H5 ]) ].
repeat (rewrite homothetie_neg2; auto).
intros.
apply similitudes_meme_centre_commutent with (3 := H0) (4 := H1); auto.
auto with real.
fourier.
absurd (k = 0); auto with real.
repeat (rewrite similitude_angle_nul; auto).
intros.
apply similitudes_meme_centre_commutent with (3 := H0) (4 := H1); auto.
fourier.
Qed.
 
Lemma similitude_conserve_angle :
 forall (I A B C A' B' C' : PO) (k a : R),
 k > 0 ->
 A <> B ->
 A <> C ->
 A' = similitude I k a A ->
 B' = similitude I k a B ->
 C' = similitude I k a C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C').
intros.
elim
 similitude_decomposition with (I := I) (M := A) (M' := A') (k := k) (a := a);
 [ intros A1 H7; elim H7; intros H8 H9; try clear H7 | auto | auto ].
elim
 similitude_decomposition with (I := I) (M := B) (M' := B') (k := k) (a := a);
 [ intros B1 H7; elim H7; intros H10 H11; try clear H7; try exact H11
 | auto
 | auto ].
elim
 similitude_decomposition with (I := I) (M := C) (M' := C') (k := k) (a := a);
 [ intros C1 H7; elim H7; intros H12 H13; try clear H7; try exact H13
 | auto
 | auto ].
cut (A1 <> B1); intros.
cut (A1 <> C1); intros.
cut (cons_AV (vec A B) (vec A C) = cons_AV (vec A1 B1) (vec A1 C1)); intros.
rewrite H7.
apply
 (homothetie_conserve_angle (I:=I) (A:=A1) (B:=B1) (C:=C1) (A':=A') (B':=B')
    (C':=C') (k:=k)); auto with real.
apply
 (rotation_conserve_angle (I:=I) (A:=A) (B:=B) (C:=C) (A':=A1) (B':=B1)
    (C':=C1) (a:=a)); auto.
apply image_bipoint_distinct with (2 := H8) (3 := H12); auto.
apply image_bipoint_distinct with (2 := H8) (3 := H10); auto.
Qed.
 
Lemma distance_similitude :
 forall (k a : R) (I A B A' B' : PO),
 k > 0 ->
 A' = similitude I k a A ->
 B' = similitude I k a B -> distance A' B' = k * distance A B.
intros.
elim
 similitude_decomposition with (I := I) (M := A) (M' := A') (k := k) (a := a);
 [ intros A1 H7; elim H7; intros H8 H9; try clear H7 | auto | auto ].
elim
 similitude_decomposition with (I := I) (M := B) (M' := B') (k := k) (a := a);
 [ intros B1 H7; elim H7; intros H10 H11; try clear H7; try exact H11
 | auto
 | auto ].
cut (distance A1 B1 = distance A B); intros.
rewrite <- H2.
rewrite (distance_homothetie (k:=k) (I:=I) (A:=A1) (A':=A') (B:=B1) (B':=B'));
 auto.
rewrite Rabs_right; auto.
red in |- *; auto.
apply rotation_isometrie with (1 := H8) (2 := H10).
Qed.