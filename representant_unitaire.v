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


Require Export orthogonalite.
Set Implicit Arguments.
Unset Strict Implicit.
Hint Resolve distance_non_nulle scalaire_positif: geo.
 
Lemma existence_unitaire :
 forall A B : PO,
 A <> B ->
 exists C : PO,
   alignes A B C /\
   scalaire (vec A C) (vec A C) = 1 /\ scalaire (vec A B) (vec A C) >= 0.
intros.
cut
 (ex
    (fun C : PO =>
     vec A C = mult_PP (/ sqrt (scalaire (vec A B) (vec A B))) (vec A B)));
 intros.
elim H0; intros C H1; try clear H0; try exact H1.
cut
 (/ sqrt (scalaire (vec A B) (vec A B)) *
  / sqrt (scalaire (vec A B) (vec A B)) * scalaire (vec A B) (vec A B) = 1);
 intros.
exists C.
split; [ try assumption | idtac ].
apply colineaire_alignes with (/ sqrt (scalaire (vec A B) (vec A B))); auto.
rewrite H1.
split; [ try assumption | idtac ].
Simplscal.
rewrite <- H0; ring.
Simplscal.
apply Rmult_pos; auto with *.
replace
 (/ sqrt (scalaire (vec A B) (vec A B)) *
  / sqrt (scalaire (vec A B) (vec A B))) with
 (/
  (sqrt (scalaire (vec A B) (vec A B)) * sqrt (scalaire (vec A B) (vec A B))));
 auto with real.
rewrite def_sqrt; auto.
auto with *.
auto with *.
apply Rinv_mult_distr; auto with *.
apply existence_representant_mult_vecteur; auto.
Qed.
 
Lemma scalaire_non_nul :
 forall A B C : PO,
 A <> B ->
 alignes A B C ->
 scalaire (vec A C) (vec A C) = 1 ->
 scalaire (vec A B) (vec A C) >= 0 -> scalaire (vec A B) (vec A C) <> 0.
intros.
halignes H0 ipattern:k.
rewrite H3.
replace (scalaire (vec A B) (mult_PP k (vec A B))) with
 (k * scalaire (vec A B) (vec A B)).
cut (scalaire (vec A B) (vec A B) <> 0 /\ k <> 0); intros.
cut (~ (k = 0 \/ scalaire (vec A B) (vec A B) = 0)); intros.
unfold not in |- *; intros; apply H5.
apply Rmult_integral; auto with *.
tauto.
split; [ try assumption | idtac ].
auto with geo.
elim (classic (k = 0)); auto; intros.
rewrite H4 in H3.
rewrite H3 in H1.
absurd (0 = 1); auto with *.
rewrite <- H1.
Simplscal.
Simplscal.
Qed.
Hint Resolve scalaire_non_nul: geo.
 
Lemma unicite_representant_unitaire :
 forall A B C D : PO,
 A <> B ->
 alignes A B C ->
 scalaire (vec A C) (vec A C) = 1 ->
 scalaire (vec A B) (vec A C) >= 0 ->
 alignes A B D ->
 scalaire (vec A D) (vec A D) = 1 ->
 scalaire (vec A B) (vec A D) >= 0 -> C = D.
intros.
halignes H0 ipattern:k.
halignes H3 ipattern:k0.
cut (k = k0); intros.
apply conversion_PP with (a := 1) (b := 1); auto with *.
RingPP2 H6.
RingPP2 H7.
rewrite H8; RingPP.
apply resolution; auto.
replace k with
 (k * scalaire (vec A B) (vec A C) * / scalaire (vec A B) (vec A C)).
replace (k * scalaire (vec A B) (vec A C)) with
 (scalaire (mult_PP k (vec A B)) (vec A C)).
rewrite <- H6; rewrite H1.
replace (1 * / scalaire (vec A B) (vec A C)) with
 (/ scalaire (vec A B) (vec A C)); try ring.
apply Rinv_le_pos; auto with geo real.
Simplscal.
field.
auto with geo.
replace k0 with
 (k0 * scalaire (vec A B) (vec A D) * / scalaire (vec A B) (vec A D)).
replace (k0 * scalaire (vec A B) (vec A D)) with
 (scalaire (mult_PP k0 (vec A B)) (vec A D)).
rewrite <- H7; rewrite H4.
replace (1 * / scalaire (vec A B) (vec A D)) with
 (/ scalaire (vec A B) (vec A D)); try ring.
apply Rinv_le_pos; auto with geo real.
Simplscal.
field.
auto with geo.
cut (scalaire (vec A C) (vec A C) = scalaire (vec A D) (vec A D)); intros.
rewrite H7 in H8; rewrite H6 in H8.
replace (k * k) with
 (scalaire (mult_PP k (vec A B)) (mult_PP k (vec A B)) *
  / scalaire (vec A B) (vec A B)).
replace (k0 * k0) with
 (scalaire (mult_PP k0 (vec A B)) (mult_PP k0 (vec A B)) *
  / scalaire (vec A B) (vec A B)).
rewrite H8; auto.
field_simplify_eq.
Simplscal.
auto with geo.
field_simplify_eq.
Simplscal.
auto with geo.
rewrite H4; auto.
Qed.
Parameter representant_unitaire : PP -> PP.
 
Axiom
  def_representant_unitaire :
    forall A B C : PO,
    A <> B ->
    alignes A B C ->
    scalaire (vec A C) (vec A C) = 1 ->
    scalaire (vec A B) (vec A C) >= 0 ->
    vec A C = representant_unitaire (vec A B).
 
Axiom
  def_representant_unitaire2 :
    forall A B C : PO,
    A <> B ->
    vec A C = representant_unitaire (vec A B) ->
    alignes A B C /\
    scalaire (vec A C) (vec A C) = 1 /\ scalaire (vec A B) (vec A C) >= 0.
 
Lemma existence_representant_unitaire :
 forall A B : PO,
 A <> B -> exists C : PO, vec A C = representant_unitaire (vec A B).
intros A B H; try assumption.
elim existence_unitaire with (A := A) (B := B);
 [ intros C H0; try clear existence_unitaire; try exact H0 | auto ].
exists C.
elim H0; intros H1 H2; elim H2; intros H3 H4; try clear H2 H0; try exact H4.
apply def_representant_unitaire; auto.
Qed.
 
Ltac applatit_and :=
  match goal with
  | h:(_ /\ _) |- _ => elim h; intros; clear h
  end.
 
Ltac deroule_representant_unitaire A B C :=
  elim (existence_representant_unitaire (A:=A) (B:=B)); auto; intros C;
   intros; elim (def_representant_unitaire2 (A:=A) (B:=B) (C:=C)); 
   auto; intros; applatit_and; cut (A <> C); intros;
   [ idtac | auto with geo ].
 
Lemma produit_positif_representant_unitaire :
 forall (k : R) (A B C : PO),
 A <> B :>PO ->
 k > 0 ->
 vec A C = mult_PP k (vec A B) :>PP ->
 representant_unitaire (vec A B) = representant_unitaire (vec A C).
intros.
cut (A <> C); intros.
2: apply distinct_produit_vecteur with (3 := H1); auto with real.
deroule_representant_unitaire A B ipattern:B'.
rewrite <- H3.
cut (scalaire (vec A C) (vec A B') >= 0); intros.
apply def_representant_unitaire; auto.
apply alignes_trans with B; auto.
apply colineaire_alignes with k; auto.
rewrite H1.
replace (scalaire (mult_PP k (vec A B)) (vec A B')) with
 (k * scalaire (vec A B) (vec A B')); [ idtac | Simplscal ].
apply Rmult_pos; auto with geo.
apply Rgt_ge; auto.
Qed.
 
Lemma egalite_representant_unitaire :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 representant_unitaire (vec A B) = representant_unitaire (vec A C) :>PP ->
 exists k : R, k > 0 /\ vec A C = mult_PP k (vec A B) :>PP.
intros A B C H H0; try assumption.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H3; try clear existence_representant_unitaire; rewrite <- H3
 | auto ].
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros C' H4; rewrite <- H4; intros | auto ].
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 [ intros | auto | auto ].
elim H5; intros H6 H7; try clear H5; try exact H7.
elim def_representant_unitaire2 with (A := A) (B := C) (C := C');
 [ intros | auto | auto ].
elim H8; intros H9 H10; try clear H8; try exact H10.
cut (alignes A C' C); intros; auto with geo.
assert (A <> C'); auto with geo.
halignes H8 ipattern:k.
halignes H2 ipattern:k0.
exists (k * k0).
split; [ idtac | try assumption ].
apply Rmult_gt_0_compat.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H14
 | intros H14; elim H14;
    [ intros H15; try clear H14; try exact H15 | intros H15; try exact H15 ] ].
absurd (scalaire (vec A C) (vec A C') >= 0); auto.
rewrite H12.
replace (scalaire (mult_PP k (vec A C')) (vec A C')) with
 (k * scalaire (vec A C') (vec A C')); [ idtac | Simplscal ].
rewrite H9.
replace (k * 1) with k; [ auto with real | ring ].
absurd (A = C); auto.
apply vecteur_nul_conf.
rewrite H12; rewrite H15; Ringvec.
elim Rtotal_order with (r1 := k0) (r2 := 0);
 [ intros H16; try clear total_order
 | intros H16; elim H16;
    [ intros H17; try clear H16; try exact H17 | intros H17; try exact H17 ] ].
absurd (scalaire (vec A B) (vec A B') >= 0); auto.
replace (vec A B) with (mult_PP (/ k0) (vec A B')); [ Simplscal | idtac ].
rewrite H6.
replace (/ k0 * 1) with (/ k0); [ idtac | ring ].
cut (/ k0 < 0); intros; auto with real.
rewrite H13.
cut (k0 <> 0); intros; auto with real.
Fieldvec k0.
absurd (scalaire (vec A B') (vec A B') = 1); auto.
rewrite H13; rewrite H17; Simplscal.
replace (0 * 0 * scalaire (vec A B) (vec A B)) with 0;
 [ auto with real | ring ].
rewrite H12; rewrite <- H1; rewrite H13; Ringvec.
Qed.
 
Lemma representant_unitaire_bis :
 forall A B : PO,
 A <> B :>PO ->
 representant_unitaire (representant_unitaire (vec A B)) =
 representant_unitaire (vec A B) :>PP.
intros A B H; try assumption.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H3; try clear existence_representant_unitaire; rewrite <- H3
 | auto ].
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 [ intros | auto | auto ].
elim H1; intros H2 H4; try clear H1; try exact H4.
cut (A <> B'); intros; auto with geo.
elim existence_representant_unitaire with (A := A) (B := B');
 [ intros C' H5; rewrite <- H5; intros | auto ].
elim def_representant_unitaire2 with (A := A) (B := B') (C := C');
 [ intros | auto | auto ].
elim H7; intros H8 H9; try clear H7; try exact H9.
cut (A <> C'); intros; auto with geo.
halignes H6 ipattern:k.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H13
 | intros H13;
    (elim H13;
      [ intros H14; try clear H13
      | intros H14; try clear H13; try exact H14 ]) ].
absurd (scalaire (vec A B') (vec A C') >= 0); auto.
rewrite H10.
replace (scalaire (vec A B') (mult_PP k (vec A B'))) with
 (k * scalaire (vec A B') (vec A B')); [ idtac | Simplscal ].
rewrite H2.
replace (k * 1) with k; [ auto with real | ring ].
absurd (A = C'); auto with geo.
apply vecteur_nul_conf.
rewrite H10; rewrite H14; Ringvec.
elim (classic (k = 1)); intros.
rewrite H10; rewrite H11; Ringvec.
absurd (scalaire (vec A C') (vec A C') = 1); auto.
rewrite H10; Simplscal; rewrite H2.
replace (k * k * 1) with (Rsqr k) by (unfold Rsqr; ring).
red in |- *; intros; apply H11.
apply Rsqr_inj; auto with real.
rewrite H12; unfold Rsqr in |- *; ring.
Qed.
Hint Resolve representant_unitaire_bis: geo.
 
Lemma oppose_representant_unitaire :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 representant_unitaire (vec A C) =
 mult_PP (-1) (representant_unitaire (vec A B)) :>PP ->
 exists k : R, k < 0 /\ vec A C = mult_PP k (vec A B) :>PP.
intros A B C H H0; try assumption.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H3; try clear existence_representant_unitaire; rewrite <- H3
 | auto ].
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros C' H4; rewrite <- H4; intros | auto ].
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 [ intros | auto | auto ].
elim H5; intros H6 H7; try clear H5; try exact H7.
elim def_representant_unitaire2 with (A := A) (B := C) (C := C');
 [ intros | auto | auto ].
elim H8; intros H9 H10; try clear H8; try exact H10.
cut (representant_unitaire (vec A C) = representant_unitaire (vec A C'));
 intros.
elim egalite_representant_unitaire with (A := A) (B := C) (C := C');
 [ intros k H12; try clear egalite_representant_unitaire; try exact H12
 | auto with geo
 | auto with geo
 | auto with geo ].
elim H12; intros H13 H14; try clear H12; try exact H14.
cut (representant_unitaire (vec A B) = representant_unitaire (vec A B'));
 intros.
elim egalite_representant_unitaire with (A := A) (B := B) (C := B');
 [ intros k0 H12; try clear egalite_representant_unitaire; try exact H12
 | auto with geo
 | auto with geo
 | auto with geo ].
elim H12; intros H15 H16; try clear H12; try exact H16.
cut (k <> 0); auto with real; intros.
replace (vec A C) with (mult_PP (/ k) (vec A C')); idtac.
rewrite H1; rewrite H16.
exists (- (/ k * k0)).
split; [ idtac | Ringvec ].
cut (/ k * k0 > 0); intros; auto with real.
apply Rmult_gt_0_compat; auto with *.
rewrite H14.
Fieldvec k.
rewrite H3; (symmetry  in |- *; auto with geo).
rewrite H4; (symmetry  in |- *; auto with geo).
Qed.
 
Lemma produit_negatif_representant_unitaire :
 forall (k : R) (A B C : PO),
 A <> B ->
 k < 0 ->
 vec A C = mult_PP k (vec A B) ->
 representant_unitaire (vec A C) =
 mult_PP (-1) (representant_unitaire (vec A B)).
intros.
cut (A <> C); intros.
2: apply distinct_produit_vecteur with (3 := H1); auto.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H3; try clear existence_representant_unitaire; try exact H3
 | auto ].
rewrite <- H3.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 [ intros; elim H5; intros H6 H7; try clear H5; try exact H6 | auto | auto ].
cut (- scalaire (vec A C) (vec A B') >= 0); intros.
symmetry  in |- *.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := B') (k := -1); intros D H9;
 try clear existence_representant_mult_vecteur; rewrite <- H9.
apply def_representant_unitaire; auto.
apply alignes_trans with B; auto.
apply colineaire_alignes with k; auto.
halignes H4 ipattern:k0.
apply colineaire_alignes with (- k0); auto.
rewrite H9; rewrite H8; Ringvec.
rewrite H9; Simplscal; auto.
rewrite H9; Simplscal; auto.
rewrite H1; Simplscal.
apply Rmult_pos; auto.
apply Rgt_ge; auto with real.
auto with real.
Qed.
 
Lemma alignes_representant_unitaire :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 alignes A B C ->
 representant_unitaire (vec A B) = representant_unitaire (vec A C) \/
 representant_unitaire (vec A C) =
 mult_PP (-1) (representant_unitaire (vec A B)).
intros.
halignes H1 ipattern:k.
elim Rtotal_order with (r1 := k) (r2 := 0);
 [ intros H3; try clear total_order
 | intros H3; elim H3;
    [ intros H4; try clear H3 total_order
    | intros H4; try clear H3 total_order; try exact H4 ] ].
right; try assumption.
apply produit_negatif_representant_unitaire with k; auto.
absurd (k = 0); auto.
contrapose H0.
apply (produit_zero_conf H2); auto.
left; try assumption.
apply produit_positif_representant_unitaire with k; auto.
Qed.
