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


Require Export aire_signee.
Require Export metrique_triangle.
Set Implicit Arguments.
Unset Strict Implicit.
Parameters (O : PO) (I : PO) (J : PO).
Hypothesis OIJ : repere_orthonormal_direct O I J.
Hint Resolve OIJ: geo.
 
Lemma OIJ_repere_ortho : repere_orthonormal O I J.
auto with geo.
Qed.
 
Lemma OIJ_repere : repere O I J.
auto with geo.
Qed.
 
Lemma OI_distincts : O <> I.
elim OIJ; intros.
auto with geo.
elim H0; intros; auto with geo.
Qed.
 
Lemma OJ_distincts : O <> J.
elim OIJ; intros.
elim H0; intros; auto with geo.
Qed.
Hint Resolve OIJ_repere_ortho OIJ_repere OI_distincts OJ_distincts: geo.
 
Lemma IJ_distincts : I <> J.
cut (repere_orthonormal O I J); intros; auto with geo.
elim H; intros.
apply non_alignes_distincts2 with O; auto.
apply orthogonal_non_alignes; auto with geo.
Qed.
Hint Resolve IJ_distincts: geo.
 
Ltac deroule_OIJ :=
  elim OIJ; intro; intros toto; elim toto; intros; clear toto;
   cut (distance O I = 1); intros; [ idtac | auto with geo ];
   cut (distance O J = 1); intros; [ idtac | auto with geo ].
 
Lemma unite_aire : aire (vec O I) (vec O J) = 1.
intros.
deroule_OIJ.
rewrite def_aire; auto with geo.
rewrite (def_Sin (A:=O) (B:=I) (C:=J) (D:=J)); auto with geo.
rewrite H1; rewrite H2; rewrite H3; ring.
Qed.
 
Lemma opp_unite_aire : aire (vec O J) (vec O I) = -1.
intros.
deroule_OIJ.
rewrite def_aire; auto with geo.
rewrite Sin_opp; auto with geo.
rewrite (def_Sin (A:=O) (B:=I) (C:=J) (D:=J)); auto with geo.
rewrite H1; rewrite H2; rewrite H3; ring.
Qed.
Parameter det : PP -> PP -> R.
 
Axiom
  determinant_def :
    forall (A B C D : PO) (x y x' y' : R),
    vec A B = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) ->
    vec C D = add_PP (mult_PP x' (vec O I)) (mult_PP y' (vec O J)) ->
    det (vec A B) (vec C D) = x * y' + - (y * x').
 
Lemma aire_coordonnees :
 forall (M N : PO) (x y x' y' : R),
 vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) ->
 vec O N = add_PP (mult_PP x' (vec O I)) (mult_PP y' (vec O J)) ->
 aire (vec O M) (vec O N) = x * y' + - (y * x').
intros.
rewrite H.
elim
 existence_representant_mult_vecteur with (A := O) (B := O) (C := I) (k := x);
 [ intros A H1; rewrite <- H1 ].
elim
 existence_representant_mult_vecteur with (A := O) (B := O) (C := J) (k := y);
 [ intros B H2; rewrite <- H2 ].
rewrite aire_distrib_r.
rewrite H1.
rewrite aire_colineaire_l.
rewrite H2.
rewrite aire_colineaire_l.
rewrite H0.
elim
 existence_representant_mult_vecteur
  with (A := O) (B := O) (C := I) (k := x'); [ intros C H3; rewrite <- H3 ].
elim
 existence_representant_mult_vecteur
  with (A := O) (B := O) (C := J) (k := y'); [ intros D H4; rewrite <- H4 ].
repeat rewrite aire_distrib_l.
rewrite H3.
repeat rewrite aire_colineaire_r.
rewrite H4.
repeat rewrite aire_colineaire_r.
repeat rewrite aire_ABAB.
rewrite unite_aire.
rewrite opp_unite_aire.
ring.
Qed.
 
Lemma determinant_aire :
 forall A B C D : PO, det (vec A B) (vec C D) = aire (vec A B) (vec C D).
intros.
elim composantes_vecteur with (O := O) (I := I) (J := J) (M := A) (N := B);
 [ intros x H; elim H;
    [ intros y H0; try clear H composantes_vecteur; try exact H0 ]
 | auto with geo ].
elim composantes_vecteur with (O := O) (I := I) (J := J) (M := C) (N := D);
 [ intros x' H1; elim H1;
    [ intros y' H2; try clear H1 composantes_vecteur; try exact H2 ]
 | auto with geo ].
rewrite
 (determinant_def (A:=A) (B:=B) (C:=C) (D:=D) (x:=x) (y:=y) (x':=x') (y':=y'))
 ; auto.
generalize H0 H2.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 [ intros E H3; rewrite <- H3 ].
elim existence_representant_vecteur with (A := O) (B := C) (C := D);
 [ intros F H4; rewrite <- H4 ].
intros; symmetry  in |- *.
apply aire_coordonnees; auto.
Qed.
 
Lemma determinant_antisymetrique :
 forall A B C D : PO, det (vec A B) (vec C D) = - det (vec C D) (vec A B).
intros.
repeat rewrite determinant_aire.
rewrite aire_anti_symetrique; auto.
Qed.
 
Lemma determinant_colinearite :
 forall (k : R) (A B C D : PO),
 vec C D = mult_PP k (vec A B) -> det (vec A B) (vec C D) = 0.
intros.
repeat rewrite determinant_aire.
apply (aire_colinearite H).
Qed.
 
Lemma determinant_nul_colinearite :
 forall A B C D : PO,
 A <> B ->
 det (vec A B) (vec C D) = 0 -> exists k : _, vec C D = mult_PP k (vec A B).
intros A B C D H; try assumption.
rewrite determinant_aire; intros.
apply aire_nulle_colineaires; auto.
Qed.
 
Lemma alignement_determinant :
 forall A B M : PO, alignes A B M -> det (vec A B) (vec A M) = 0.
intros.
rewrite determinant_aire.
apply aire_alignement; auto.
Qed.
 
Lemma determinant_nul_alignement :
 forall A B M : PO, det (vec A B) (vec A M) = 0 -> alignes A B M.
intros.
discrimine A B.
elim determinant_nul_colinearite with (A := A) (B := B) (C := A) (D := M);
 [ intros k H1; try clear determinant_nul_colinearite; try exact H1
 | auto
 | auto ].
apply colineaire_alignes with k; auto.
Qed.
 
Lemma determinant_colineaire_l :
 forall (k : R) (A B C D : PO),
 det (mult_PP k (vec A B)) (vec C D) = k * det (vec A B) (vec C D).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 [ intros E H1; rewrite <- H1 ].
repeat rewrite determinant_aire.
rewrite H1.
apply aire_colineaire_l.
Qed.
 
Lemma determinant_distrib_l :
 forall A B C D E F : PO,
 det (vec A B) (add_PP (vec C D) (vec E F)) =
 det (vec A B) (vec C D) + det (vec A B) (vec E F).
intros.
elim
 existence_representant_som_vecteur with (A := C) (B := D) (C := E) (D := F);
 [ intros G H; try clear existence_representant_som_vecteur; rewrite <- H ].
repeat rewrite determinant_aire.
rewrite H.
apply aire_distrib_l.
Qed.
 
Lemma determinant_ordre_cycle :
 forall A B C D E F : PO, det (vec B C) (vec B A) = det (vec A B) (vec A C).
intros.
repeat rewrite determinant_aire.
apply aire_ordre_cycle.
Qed.
 
Lemma determinant_aire_triangle :
 forall A B C : PO,
 aire_triangle A B C = / 2 * Rabs (det (vec A B) (vec A C)).
unfold aire_triangle in |- *; intros.
repeat rewrite determinant_aire; auto.
Qed.
 
Lemma calcul_distance_droite :
 forall A B C : PO,
 A <> B ->
 distance_droite C (droite A B) =
 Rabs (det (vec A B) (vec A C)) / distance A B.
intros A B C H0; try assumption.
elim existence_projete_orthogonal with (A := A) (B := B) (C := C);
 [ intros H H1; try clear existence_projete_orthogonal; try exact H1 | auto ].
repeat rewrite determinant_aire.
rewrite (distance_droite_def (A:=A) (B:=B) (C:=C) (H:=H)); auto.
rewrite (aire_avec_projete (A:=A) (B:=B) (C:=C) (H:=H)); auto.
replace (distance C H) with (distance H C); auto with geo.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
rewrite aire_orthogonal; auto with geo.
unfold Rdiv in |- *.
cut (distance A B <> 0); intros; auto with geo.
RReplace (distance A B * distance H C * / distance A B)
 (distance A B * / distance A B * distance H C).
RReplace (distance A B * / distance A B) 1.
ring.
Qed.