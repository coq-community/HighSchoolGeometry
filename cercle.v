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


Require Export isocele.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition cercle (O : PO) (r : R) (M : PO) : Prop := distance O M = r.
 
Lemma cercle_isocele :
 forall (O A B : PO) (r : R), cercle O r A -> cercle O r B -> isocele O A B.
unfold cercle, isocele in |- *; intros.
rewrite H; rewrite H0; auto.
Qed.
 
Lemma existence_rayon : forall O A : PO, cercle O (distance O A) A.
unfold cercle in |- *; intros; auto.
Qed.
 
Lemma isocele_cercle :
 forall O A B : PO, isocele O A B -> cercle O (distance O A) B.
unfold cercle, isocele in |- *; intros; auto.
Qed.
 
Definition circonscrit (O A B C : PO) : Prop :=
  isocele O A B /\ isocele O A C.
 
Lemma circonscrit_isocele :
 forall O A B C : PO, circonscrit O A B C -> isocele O B C.
unfold circonscrit, isocele in |- *; intros; auto.
elim H; intros; auto.
rewrite <- H0; rewrite <- H1; auto.
Qed.
 
Lemma circonscrit_permute :
 forall O A B C : PO, circonscrit O B C A -> circonscrit O A B C.
unfold circonscrit in |- *; intros.
elim H; intros; split; auto with geo.
lapply (circonscrit_isocele (O:=O) (A:=B) (B:=C) (C:=A)); auto with geo.
Qed.
 
Lemma circonscrit_distinct1 :
 forall O A B C : PO, O <> A -> circonscrit O A B C -> O <> B.
unfold circonscrit, isocele in |- *; intros.
elim H0; [ intros H1 H2; try clear H0; try exact H2 ].
apply isometrie_distinct with (2 := H1); auto.
Qed.
 
Lemma circonscrit_distinct2 :
 forall O A B C : PO, O <> A -> circonscrit O A B C -> O <> C.
unfold circonscrit, isocele in |- *; intros.
elim H0; [ intros H1 H2; try clear H0; try exact H2 ].
apply isometrie_distinct with (2 := H2); auto.
Qed.
 
Lemma circonscrit_distinct3 :
 forall O A B C : PO, O <> B -> circonscrit O A B C -> O <> A.
intros.
assert (circonscrit O B C A).
apply circonscrit_permute.
apply circonscrit_permute; auto.
apply circonscrit_distinct2 with (2 := H1); auto.
Qed.
 
Definition cercle_rayon (O A M : PO) := isocele O A M.
 
Definition tangente_cercle (O A T M : PO) :=
  cercle_rayon O A T /\ orthogonal (vec T M) (vec T O).
 
Definition cercle_diametre (A B M : PO) :=
  exists O : PO, circonscrit O A B M /\ O = milieu A B.
 
Definition sont_cocycliques (A B C D : PO) :=
  ex (fun O : PO => circonscrit O A B C /\ circonscrit O A B D).
 
Ltac hcercle H :=
  generalize H;
   unfold cercle_diametre, tangente_cercle, cercle_rayon, cercle,
    sont_cocycliques, circonscrit, isocele in |- *; 
   intros; repeat applatit_and; try split; auto with geo.
 
Ltac icercle :=
  unfold cercle_diametre, tangente_cercle, cercle_rayon, cercle,
   sont_cocycliques, circonscrit, isocele in |- *; 
   intros; repeat applatit_and; try split; auto with geo.
 
Lemma cercle_diametre_permute :
 forall A B C : PO, cercle_diametre A B C -> cercle_diametre B A C.
icercle.
elim H;
 [ intros O H0; elim H0;
    [ intros H1 H2; elim H1;
       [ intros H3 H4; try clear H1 H0 H; try exact H4 ] ] ].
exists O; split; auto with geo.
split; [ auto | idtac ].
rewrite <- H3; auto.
Qed.
Hint Immediate cercle_diametre_permute: geo.
 
Lemma cercle_diametre_trivial : forall A B : PO, cercle_diametre A B A.
icercle.
discrimine A B.
exists B; split; auto with geo.
soit_milieu A B ipattern:M.
exists M.
split; auto.
split; auto with geo.
Qed.
 
Lemma cercle_diametre_trivial2 : forall A B : PO, cercle_diametre A B B.
icercle.
discrimine A B.
exists B; split; auto with geo.
soit_milieu A B ipattern:M.
exists M.
split; auto.
split; auto with geo.
Qed.
Hint Resolve cercle_diametre_trivial2 cercle_diametre_trivial: geo.
 
Lemma circonscrit_diametre :
 forall A B C D O : PO,
 circonscrit O A B C -> O = milieu A D -> cercle_diametre A D B.
icercle.
exists O.
split; [ split; [ auto with geo | try assumption ] | try assumption ].
Qed.
 
Lemma cercle_trivial :
 forall A B C D O : PO,
 circonscrit O A B C -> O = milieu A D -> sont_cocycliques A B C D.
icercle.
exists O.
split; [ split; [ try assumption | try assumption ] | try assumption ].
split; [ try assumption | auto with geo ].
Qed.
 
Lemma cercle_diametre_degenere :
 forall A B M : PO, A = B -> cercle_diametre A B M -> A = M.
intros A B M H; try assumption.
rewrite H; icercle.
elim H0;
 [ intros O' H1; elim H1;
    [ intros H2 H3; elim H2;
       [ intros H4 H5; try clear H2 H1 H0; try exact H5 ] ] ].
assert (O' = B).
rewrite (milieu_trivial B); auto.
rewrite <- H0.
apply distance_refl1.
rewrite <- H5; rewrite <- H0; auto with geo.
Qed.
Require Export dilatations.
 
Lemma existence_rayon_diametre :
 forall A B O : PO,
 cercle_rayon O A B -> exists C : PO, cercle_diametre A C B.
unfold cercle_rayon, isocele in |- *; intros.
symetrique O A ipattern:M.
exists M.
icercle.
exists O.
auto with geo.
Qed.
 
Lemma existence_point_cercle : forall O A : PO, 
exists C, cercle_rayon O A C.
Proof.
intros.
exists A.
unfold cercle_rayon.
unfold isocele.
auto with geo.
Qed.


Lemma alignes_diametre :
 forall A B A' : PO,
 alignes A A' B -> cercle_diametre A A' B -> B = A \/ B = A'.
unfold cercle_diametre in |- *; intros.
elim H0;
 [ intros O H1; elim H1; [ intros H2 H3; try clear H1 H0; try exact H3 ] ].
hcercle H2.
discrimine A A'.
assert (O = A).
rewrite H3; rewrite <- H0; rewrite <- milieu_trivial; auto.
rewrite <- H0.
right; try assumption.
rewrite <- H5.
symmetry  in |- *.
assert (distance O B = 0); auto with geo.
rewrite <- H4; rewrite <- H5; auto with geo.
halignes H ipattern:k.
elim (classic (k = 0)); intros.
left; symmetry  in |- *.
apply (produit_zero_conf H5); auto.
discrimine O A.
left; symmetry  in |- *.
assert (distance O B = 0); auto with geo.
rewrite <- H4; rewrite <- H7; auto with geo.
right; try assumption.
assert (vec A B = mult_PP (2 * k) (vec A O)).
rewrite H5.
rewrite (milieu_vecteur_double H3); auto.
Ringvec.
assert (k = 1).
assert (vec O B = mult_PP (1 + - (2 * k)) (vec O A)).
VReplace (vec O B) (add_PP (vec A B) (vec O A)).
rewrite H8; Ringvec.
assert (Rsqr (1 + - (2 * k)) = 1).
assert (Rsqr (distance O A) = Rsqr (1 + - (2 * k)) * Rsqr (distance O A)).
pattern (distance O A) at 1 in |- *.
rewrite H4.
unfold Rsqr in |- *; repeat rewrite <- carre_scalaire_distance.
rewrite H9.
Simplscal.
apply Rmult_eq_reg_l with (Rsqr (distance O A)).
pattern (Rsqr (distance O A)) at 2 in |- *; rewrite H10 in |- *;  ring.
unfold Rsqr in |- *; apply Rmult_integral_contrapositive.
split; auto with geo.
assert (Rsqr (1 + - (2 * k)) + - Rsqr 1 = 0).
rewrite H10; unfold Rsqr in |- *; ring.
assert (2 * (1 + - k) * - (2 * k) = 0).
RReplace (- (2 * k)) (1 + - (2 * k) + -1).
RReplace (2 * (1 + - k)) (1 + - (2 * k) + 1).
rewrite <- H11; unfold Rsqr in |- *; ring.
assert (1 + - k = 0).
apply Rmult_eq_reg_l with (- (2 * k)); auto with real.
RReplace (- (2 * k) * 0) 0.
apply Rmult_eq_reg_l with 2; auto with real.
RReplace (2 * 0) 0.
rewrite <- H12; ring.
RReplace k (k + 0).
rewrite <- H13; ring.
apply egalite_vecteur_point with A.
rewrite H5; rewrite H9; Ringvec.
Qed.
