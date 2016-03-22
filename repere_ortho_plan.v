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


Require Export repere_plan.
Require Export distance_euclidienne.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition repere_orthogonal (O I J : PO) :=
  repere O I J /\ scalaire (vec O I) (vec O J) = 0.
 
Lemma triangle_rectangle_repere :
 forall O I J : PO,
 O <> I ->
 O <> J -> orthogonal (vec O I) (vec O J) -> repere_orthogonal O I J.
intros; red in |- *.
cut (scalaire (vec O I) (vec O J) = 0); intros.
split; [ idtac | try assumption ].
red in |- *; red in |- *; red in |- *; intros.
halignes H3 ipattern:k.
rewrite H4 in H2.
rewrite scalaire_mult_d in H2.
elim (classic (k = 0)); intros.
rewrite H5 in H4.
absurd (O = J); auto.
apply vecteur_nul_conf.
rewrite H4; Ringvec.
absurd (O = I); auto.
apply distance_nulle.
elim Rmult_integral with (r1 := k) (r2 := scalaire (vec O I) (vec O I));
 [ intros H6; try clear without_div_Od
 | intros H6; try clear without_div_Od; try exact H6
 | auto ].
absurd (k = 0); auto.
apply def_orthogonal; auto.
Qed.
 
Definition repere_orthonormal (O I J : PO) :=
  scalaire (vec O I) (vec O J) = 0 /\
  scalaire (vec O I) (vec O I) = 1 /\ scalaire (vec O J) (vec O J) = 1.
 
Lemma orthonormal_orthogonal :
 forall O I J : PO, repere_orthonormal O I J -> repere_orthogonal O I J.
unfold repere_orthonormal in |- *; intros.
elim H; intros H0 H1; elim H1; intros H2 H3; try clear H1 H; try exact H3.
apply triangle_rectangle_repere; auto with geo.
Qed.
Hint Resolve orthonormal_orthogonal: geo.
 
Lemma orthonormal_repere :
 forall O I J : PO, repere_orthonormal O I J -> repere O I J.
intros.
cut (repere_orthogonal O I J); intros; auto with geo.
elim H0; auto.
Qed.
Hint Resolve orthonormal_repere: geo.
 
Lemma orthonormal_non_alignes :
 forall O I J : PO, repere_orthonormal O I J -> ~ alignes O I J.
intros.
cut (repere O I J); intros; auto with geo.
Qed.
Hint Resolve orthonormal_non_alignes: geo.
 
Lemma orthogonal_paralleles :
 forall A B C E F : PO,
 A <> B ->
 A <> C ->
 orthogonal (vec A B) (vec A C) ->
 orthogonal (vec E F) (vec A B) ->
 exists k : R, vec E F = mult_PP k (vec A C).
intros.
cut (repere_orthogonal A B C); intros.
elim H3; intros.
generalize (composantes_vecteur (O:=A) (I:=B) (J:=C) E F); intros.
elim H6;
 [ intros x H7; elim H7; [ intros y H8; try clear H7 H6; try exact H8 ]
 | auto ].
cut (scalaire (vec E F) (vec A B) = 0); auto with geo; intros.
cut (x = 0); intros.
rewrite H8; rewrite H7.
exists y.
Ringvec.
cut (x * scalaire (vec A B) (vec A B) = 0); intros.
elim Rmult_integral with (r1 := scalaire (vec A B) (vec A B)) (r2 := x);
 [ intros H12; try clear without_div_Od; try trivial
 | intros H12; try trivial
 | try trivial ].
absurd (scalaire (vec A B) (vec A B) = 0); auto with geo.
rewrite <- H7; ring.
rewrite <- H6; auto with geo.
rewrite H8.
Simplscal.
rewrite (scalaire_sym A C A B).
rewrite H5; ring.
apply triangle_rectangle_repere; auto with geo.
Qed.
 
Lemma orthogonal_colineaires :
 forall A B C D E F : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 orthogonal (vec A B) (vec C D) ->
 orthogonal (vec A B) (vec E F) ->
 ex (fun k : R => vec E F = mult_PP k (vec C D) :>PP).
intros.
elim existence_representant_vecteur with (A := A) (B := C) (C := D);
 intros C1 H5; try clear existence_representant_vecteur; 
 try exact H5.
rewrite <- H5.
elim orthogonal_paralleles with (A := A) (B := B) (C := C1) (E := E) (F := F);
 [ intros k H3; try clear orthogonal_paralleles; try exact H3
 | auto
 | auto
 | auto
 | auto with geo ].
exists k; auto.
apply distinct_egalite_vecteur with (2 := H5); auto.
rewrite H5; auto with geo.
Qed.
 
Lemma scalaire_coordonnees :
 forall (O I J M N : PO) (x y x' y' : R),
 repere_orthonormal O I J ->
 vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) ->
 vec O N = add_PP (mult_PP x' (vec O I)) (mult_PP y' (vec O J)) ->
 scalaire (vec O M) (vec O N) = x * x' + y * y'.
unfold repere_orthonormal in |- *; intros.
rewrite H0; rewrite H1.
Simplscal.
elim H; intros H4 H5; elim H5; intros H6 H7; try clear H5 H; try exact H7.
rewrite H7; rewrite H6; rewrite H4; rewrite scalaire_sym; rewrite H4; ring.
Qed.
 
Lemma scalaire_composantes_ABCD :
 forall (O I J A B C D : PO) (x y x' y' : R),
 repere_orthonormal O I J ->
 vec A B = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) ->
 vec C D = add_PP (mult_PP x' (vec O I)) (mult_PP y' (vec O J)) ->
 scalaire (vec A B) (vec C D) = x * x' + y * y'.
intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 [ intros M H20 ].
elim existence_representant_vecteur with (A := O) (B := C) (C := D);
 [ intros N H21 ].
rewrite <- H20; rewrite <- H21.
rewrite
 (scalaire_coordonnees (O:=O) (I:=I) (J:=J) (M:=M) (N:=N) (x:=x) (y:=y)
    (x':=x') (y':=y')); auto with geo.
rewrite H20; auto.
rewrite H21; auto.
Qed.
 
Lemma coordonnees_scalaire_base :
 forall O I J M : PO,
 repere_orthonormal O I J ->
 vec O M =
 add_PP (mult_PP (scalaire (vec O M) (vec O I)) (vec O I))
   (mult_PP (scalaire (vec O M) (vec O J)) (vec O J)).
intros.
elim existence_coordonnees with (O := O) (I := I) (J := J) (M := M);
 [ intros x H1; elim H1; intros y H2; try clear H1; try exact H2
 | auto with geo ].
elim H; intros H1 H11; elim H11; intros H3 H4; try clear H11; try exact H4.
cut (x = scalaire (vec O M) (vec O I) /\ y = scalaire (vec O M) (vec O J));
 intros.
elim H0; intros H6 H7; try clear H5; try exact H7.
rewrite <- H7; rewrite <- H6; auto.
rewrite H2.
split; [ try assumption | idtac ].
Simplscal.
rewrite H3; rewrite scalaire_sym; rewrite H1; ring.
Simplscal.
rewrite H4; rewrite H1; ring.
Qed.
 
Lemma distance_coordonnees :
 forall (O I J M : PO) (x y : R),
 repere_orthonormal O I J ->
 vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) :>PP ->
 distance O M = sqrt (Rsqr x + Rsqr y) :>R.
unfold distance in |- *; intros.
rewrite
 (scalaire_coordonnees (O:=O) (I:=I) (J:=J) (M:=M) (N:=M) (x:=x) (y:=y)
    (x':=x) (y':=y)); eauto.
Qed.
Hint Resolve distance_coordonnees: geo.