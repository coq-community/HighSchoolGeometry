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


Require Export parallelisme_concours.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter scalaire : PP -> PP -> R.
 
Axiom scalaire_positif : forall A B : PO, scalaire (vec A B) (vec A B) >= 0.
 
Axiom
  scalaire_non_degenere :
    forall A B : PO, scalaire (vec A B) (vec A B) = 0 -> vec A B = zero.
 
Axiom
  scalaire_sym :
    forall A B C D : PO,
    scalaire (vec A B) (vec C D) = scalaire (vec C D) (vec A B).
 
Axiom
  scalaire_somme_g :
    forall A B C D E F : PO,
    scalaire (add_PP (vec A B) (vec C D)) (vec E F) =
    scalaire (vec A B) (vec E F) + scalaire (vec C D) (vec E F).
 
Axiom
  scalaire_mult_g :
    forall (k : R) (A B C D : PO),
    scalaire (mult_PP k (vec A B)) (vec C D) =
    k * scalaire (vec A B) (vec C D).
 
Lemma scalaire_lineaire_g :
 forall (a b : R) (A B C D E F : PO),
 scalaire (add_PP (mult_PP a (vec A B)) (mult_PP b (vec C D))) (vec E F) =
 a * scalaire (vec A B) (vec E F) + b * scalaire (vec C D) (vec E F).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := a);
 intros B' H; try clear existence_representant_mult_vecteur; 
 rewrite <- H.
elim
 existence_representant_mult_vecteur with (A := A) (B := C) (C := D) (k := b);
 intros C' H0; try clear existence_representant_mult_vecteur; 
 rewrite <- H0.
rewrite scalaire_somme_g.
rewrite H; rewrite H0.
repeat rewrite scalaire_mult_g; auto.
Qed.
 
Lemma scalaire_lineaire_d :
 forall (a b : R) (A B C D E F : PO),
 scalaire (vec E F) (add_PP (mult_PP a (vec A B)) (mult_PP b (vec C D))) =
 a * scalaire (vec E F) (vec A B) + b * scalaire (vec E F) (vec C D).
intros.
rewrite scalaire_sym.
rewrite (scalaire_sym E F C D).
rewrite <- scalaire_lineaire_g.
elim
 existence_representant_comb_lin_vecteur
  with (A := A) (B := B) (C := C) (D := D) (a := a) (b := b); 
 intros E0 H; try clear existence_representant_comb_lin_vecteur; 
 rewrite <- H.
rewrite scalaire_sym; auto.
Qed.
 
Lemma scalaire_bilineaire :
 forall (a b c d : R) (A B C D E F G H : PO),
 scalaire (add_PP (mult_PP a (vec A B)) (mult_PP b (vec C D)))
   (add_PP (mult_PP c (vec E F)) (mult_PP d (vec G H))) =
 a * c * scalaire (vec A B) (vec E F) + a * d * scalaire (vec A B) (vec G H) +
 (b * c * scalaire (vec C D) (vec E F) + b * d * scalaire (vec C D) (vec G H)).
intros a b c d A B C D E F G I; try assumption.
elim
 existence_representant_comb_lin_vecteur
  with (A := E) (B := F) (C := G) (D := I) (a := c) (b := d); 
 intros E0 H; try clear existence_representant_comb_lin_vecteur; 
 rewrite <- H.
rewrite scalaire_lineaire_g.
rewrite H.
repeat rewrite scalaire_lineaire_d.
ring.
Qed.
 
Lemma scalaire_mult_mult :
 forall (A B C D : PO) (x y : R),
 scalaire (mult_PP x (vec A B)) (mult_PP y (vec C D)) =
 x * y * scalaire (vec A B) (vec C D) :>R.
intros A B C D x y; try assumption.
replace (mult_PP x (vec A B)) with
 (add_PP (mult_PP x (vec A B)) (mult_PP 0 (vec C D))).
replace (mult_PP y (vec C D)) with
 (add_PP (mult_PP 0 (vec A B)) (mult_PP y (vec C D))).
rewrite scalaire_bilineaire; ring.
unfold vec in |- *; RingPP.
unfold vec in |- *; RingPP.
Qed.
 
Lemma scalaire_mult_d :
 forall (k : R) (A B C D : PO),
 scalaire (vec A B) (mult_PP k (vec C D)) = k * scalaire (vec A B) (vec C D)
 :>R.
intros.
replace (mult_PP k (vec C D)) with
 (add_PP (mult_PP k (vec C D)) (mult_PP 0 (vec C D))).
rewrite scalaire_lineaire_d.
ring.
unfold vec in |- *; RingPP.
Qed.
 
Lemma scalaire_somme_d :
 forall A B C D E F : PO,
 scalaire (vec A B) (add_PP (vec C D) (vec E F)) =
 scalaire (vec A B) (vec C D) + scalaire (vec A B) (vec E F) :>R.
intros.
replace (add_PP (vec C D) (vec E F)) with
 (add_PP (mult_PP 1 (vec C D)) (mult_PP 1 (vec E F))).
rewrite scalaire_lineaire_d.
ring.
unfold vec in |- *; RingPP.
Qed.
 
Ltac Simplscal :=
  repeat rewrite scalaire_lineaire_d; repeat rewrite scalaire_lineaire_g;
   repeat rewrite scalaire_somme_g; repeat rewrite scalaire_somme_d;
   repeat rewrite scalaire_mult_g; repeat rewrite scalaire_mult_d;
   repeat rewrite scalaire_mult_mult; repeat rewrite scalaire_bilineaire;
   try (ring || ring_simplify).
 
Lemma unitaire_distincts :
 forall A B : PO, scalaire (vec A B) (vec A B) = 1 -> A <> B :>PO.
intros; unfold not in |- *; intros.
absurd (scalaire (vec A B) (vec A B) = 1); auto.
rewrite H0.
pattern (vec B B) at 1 in |- *.
replace (vec B B) with (mult_PP 0 (vec A B)).
rewrite scalaire_mult_g.
replace (0 * scalaire (vec A B) (vec B B)) with 0.
auto with *.
ring.
unfold vec in |- *; RingPP.
Qed.
 
Lemma distance_non_nulle :
 forall A B : PO, scalaire (vec A B) (vec A B) <> 0 -> A <> B :>PO.
intros; unfold not in |- *; intros.
apply H.
rewrite H0.
replace (vec B B) with (mult_PP 0 (vec A B)).
Simplscal.
unfold vec in |- *; RingPP.
Qed.
 
Lemma distance_nulle :
 forall A B : PO, scalaire (vec A B) (vec A B) = 0 :>R -> A = B.
intros.
cut (vec A B = zero); intros.
unfold vec in H0.
apply conversion_PP with (a := 1) (b := 1); auto with *.
RingPP2 H0; RingPP.
apply scalaire_non_degenere; auto.
Qed.
Hint Resolve distance_nulle unitaire_distincts distance_non_nulle: geo.
 
Lemma egalite_scalaire_alignes :
 forall A B C D : PO,
 A <> B ->
 alignes A B C ->
 alignes A B D ->
 scalaire (vec A B) (vec A C) = scalaire (vec A B) (vec A D) -> C = D.
intros.
halignes H0 ipattern:x.
halignes H1 ipattern:x0.
assert (x = x0).
apply Rmult_eq_reg_l with (scalaire (vec A B) (vec A B)); auto with geo real.
replace (scalaire (vec A B) (vec A B) * x) with
 (scalaire (vec A B) (vec A C)).
rewrite H2; rewrite H4; Simplscal.
rewrite H3; Simplscal.
apply egalite_vecteur_point with A.
rewrite H3; rewrite H5; rewrite H4; auto.
Qed.
