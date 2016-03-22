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


Require Export distance_euclidienne.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma carre_scalaire_somme :
 forall A B C D : PO,
 scalaire (add_PP (vec A B) (vec C D)) (add_PP (vec A B) (vec C D)) =
 2 * scalaire (vec A B) (vec C D) +
 (scalaire (vec A B) (vec A B) + scalaire (vec C D) (vec C D)) :>R.
intros.
VReplace (add_PP (vec A B) (vec C D))
 (add_PP (mult_PP 1 (vec A B)) (mult_PP 1 (vec C D))).
Simplscal.
rewrite (scalaire_sym C D A B); ring.
Qed.
 
Lemma difference_Pythagore :
 forall A B C : PO,
 scalaire (vec B C) (vec B C) =
 scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C) +
 -2 * scalaire (vec A B) (vec A C) :>R.
intros.
VReplace (vec B C) (add_PP (mult_PP (-1) (vec A B)) (mult_PP 1 (vec A C))).
Simplscal.
rewrite (scalaire_sym A C A B); ring.
Qed.
 
Lemma triangle_Pythagore :
 forall A B C : PO,
 scalaire (vec A B) (vec A C) = 0 <->
 scalaire (vec B C) (vec B C) =
 scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C) :>R.
intros; red in |- *.
rewrite (difference_Pythagore A B C).
split; [ intros H; try assumption | idtac ].
rewrite H.
ring.
intros H; try assumption.
cut (2 * scalaire (vec A B) (vec A C) = 0); intros.
elim Rmult_integral with (r1 := 2) (r2 := scalaire (vec A B) (vec A C));
 [ intros H1; try clear without_div_Od
 | intros H1; try clear without_div_Od; try exact H1
 | try assumption ].
absurd (2 = 0); try assumption.
discrR.
replace 0 with
 (scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C) +
  -1 * (scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C))).
pattern (scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C)) at 2
 in |- *.
rewrite <- H.
ring.
ring.
Qed.
 
Theorem Pythagore :
 forall A B C : PO,
 orthogonal (vec A B) (vec A C) <->
 Rsqr (distance B C) = Rsqr (distance A B) + Rsqr (distance A C) :>R.
intros.
unfold Rsqr in |- *; repeat rewrite <- carre_scalaire_distance.
elim (triangle_Pythagore A B C); intros.
red in |- *; split; intros.
apply H; auto with geo.
apply def_orthogonal2; auto.
Qed.
 
Lemma longueur_mediane :
 forall A B C I : PO,
 I = milieu B C ->
 Rsqr (distance A B) + Rsqr (distance A C) =
 R2 * (Rsqr (distance A I) + Rsqr (distance I B)) :>R.
intros.
unfold Rsqr, R2 in |- *; repeat rewrite <- carre_scalaire_distance.
replace (vec A B) with (add_PP (mult_PP 1 (vec A I)) (mult_PP 1 (vec I B))).
replace (vec A C) with
 (add_PP (mult_PP 1 (vec A I)) (mult_PP (-1) (vec I B))).
Simplscal.
replace (vec I B) with (mult_PP (-1) (vec I C)).
Ringvec.
rewrite <- (milieu_vecteur H).
Ringvec.
Ringvec.
Qed.
 
Lemma demi_longueur :
 forall A B I : PO,
 I = milieu A B -> Rsqr (distance A B) = R4 * Rsqr (distance A I) :>R.
intros.
unfold Rsqr, R4 in |- *; repeat rewrite <- carre_scalaire_distance.
replace (vec A B) with (mult_PP 2 (vec A I)).
Simplscal.
rewrite <- (milieu_vecteur_double H); auto.
Qed.
 
Theorem mediane :
 forall A B C I : PO,
 I = milieu B C ->
 R4 * Rsqr (distance A I) =
 R2 * (Rsqr (distance A B) + Rsqr (distance A C)) - Rsqr (distance B C) :>R.
unfold R2, R4 in |- *; intros.
rewrite (longueur_mediane A (B:=B) (C:=C) (I:=I)); auto.
rewrite (demi_longueur (A:=B) (B:=C) (I:=I)); unfold R2, R4 in |- *; auto.
rewrite (distance_sym B I); auto.
ring.
Qed.
 
Lemma rectangle_Pythagore :
 forall A B C : PO,
 orthogonal (vec A B) (vec A C) <->
 scalaire (vec B C) (vec B C) =
 scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C) :>R.
intros.
generalize (triangle_Pythagore A B C); unfold iff in |- *; intros.
elim H; intros H0 H1; try clear H; try exact H0.
split; [ intros H; try assumption | idtac ].
apply H0; auto with geo.
intros H; try assumption.
apply def_orthogonal2; auto.
Qed.
Require Export projection_orthogonale.
 
Lemma Pythagore_projete_orthogonal :
 forall A B C H : PO,
 A <> B :>PO ->
 H = projete_orthogonal A B C :>PO ->
 Rsqr (distance A C) = Rsqr (distance H A) + Rsqr (distance H C) :>R /\
 Rsqr (distance B C) = Rsqr (distance H B) + Rsqr (distance H C) :>R.
intros.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := C) (H := H);
 [ intros; auto | auto | auto ].
halignes H2 ipattern:k.
split; [ try assumption | idtac ].
elim (Pythagore H A C); intros.
apply H5.
replace (vec H A) with (mult_PP (-1) (vec A H)).
rewrite H4.
replace (mult_PP (-1) (mult_PP k (vec A B))) with (mult_PP (- k) (vec A B)).
Simplortho.
Ringvec.
Ringvec.
elim (Pythagore H B C); intros.
apply H5.
replace (vec H B) with
 (add_PP (mult_PP 1 (vec A B)) (mult_PP (- k) (vec A B))).
Simplortho.
replace (mult_PP (- k) (vec A B)) with (mult_PP (-1) (mult_PP k (vec A B))).
rewrite <- H4.
Ringvec.
Ringvec.
Qed.
 
Lemma scalaire_difference_carre :
 forall A B I M : PO,
 I = milieu A B ->
 scalaire (vec M A) (vec M B) = Rsqr (distance M I) + - Rsqr (distance I A).
intros.
unfold Rsqr in |- *; repeat rewrite <- carre_scalaire_distance.
VReplace (vec M B) (add_PP (mult_PP 1 (vec M I)) (mult_PP 1 (vec I B))).
rewrite <- (milieu_vecteur H); auto.
VReplace (mult_PP 1 (vec A I)) (mult_PP (-1) (vec I A)).
VReplace (vec M A) (add_PP (mult_PP 1 (vec M I)) (mult_PP 1 (vec I A))).
Simplscal.
rewrite (scalaire_sym M I I A); ring.
Qed.
 
Lemma egalite_scalaire_deux_projetes :
 forall A B C H K : PO,
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 K = projete_orthogonal A C B ->
 scalaire (vec A B) (vec A H) = scalaire (vec A K) (vec A C).
intros.
elim scalaire_deux_projetes with (A := A) (B := B) (C := C) (H := H) (K := K);
 [ intros H4 H5; try clear scalaire_deux_projetes; try exact H5
 | auto
 | auto
 | auto
 | auto ].
rewrite <- H4; auto.
Qed.
 
Lemma projete_distance_Rlt :
 forall A B C H : PO,
 A <> B ->
 H <> B -> H = projete_orthogonal A B C -> distance C H < distance C B.
intros.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := C) (H := H);
 [ intros | auto | auto ].
elim (Pythagore H B C); intros.
assert (Rsqr (distance C H) < Rsqr (distance C B)).
rewrite (distance_sym C B).
rewrite H5; auto.
RReplace (Rsqr (distance C H)) (Rsqr (distance C H) + 0).
assert (0 < Rsqr (distance H B)).
assert (distance H B <> 0); auto with geo.
cut (0 <= distance H B); auto with geo real.
RReplace (Rsqr (distance H B) + Rsqr (distance H C))
 (Rsqr (distance H C) + Rsqr (distance H B)).
rewrite distance_sym; auto with real.
halignes H3 ipattern:k.
VReplace (vec H B) (add_PP (vec A B) (mult_PP (-1) (vec A H))).
rewrite H7.
VReplace (add_PP (vec A B) (mult_PP (-1) (mult_PP k (vec A B))))
 (mult_PP (1 + - k) (vec A B)).
auto with geo.
apply Rsqr_incrst_0; auto with real geo.
Qed.
Parameter distance_droite : PO -> DR -> R.
 
Axiom
  distance_droite_def :
    forall A B C H : PO,
    A <> B ->
    H = projete_orthogonal A B C ->
    distance_droite C (droite A B) = distance C H.
 
Lemma existence_distance_droite :
 forall A B C : PO,
 A <> B -> exists d : R, d = distance_droite C (droite A B).
intros A B C H0; try assumption.
elim existence_projete_orthogonal with (A := A) (B := B) (C := C);
 [ intros H H1; try clear existence_projete_orthogonal; try exact H1 | auto ].
exists (distance C H).
rewrite (distance_droite_def (A:=A) (B:=B) (C:=C) (H:=H)); auto.
Qed.