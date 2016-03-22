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


Require Export Rbase.
Require Export Rfunctions.
Require Export R_sqrt.
Require Export Fourier.
 
Lemma def_sqrt : forall x : R, x >= 0 -> sqrt x * sqrt x = x.
intros.
apply sqrt_sqrt; auto with real.
Qed.
 
Lemma sqrt_pos : forall x : R, x >= 0 -> sqrt x >= 0.
intros.
apply Rle_ge.
apply sqrt_positivity; auto with real.
Qed.
 
Lemma Rmult_pos : forall x y : R, x >= 0 -> y >= 0 -> x * y >= 0.
intros.
apply Rle_ge.
apply Rmult_le_pos; auto with real.
Qed.
 
Lemma Rinv_le_pos : forall x : R, x <> 0 -> x >= 0 -> / x >= 0.
intros.
inversion H0.
apply Rle_ge.
apply Rlt_le; auto with real.
absurd (x = 0); auto.
Qed.
 
Lemma non_sqrt_zero : forall r : R, r >= 0 -> r <> 0 -> sqrt r <> 0.
unfold not in |- *; intros.
apply H0.
rewrite <- (def_sqrt r); auto.
rewrite H1; ring.
Qed.
 
Lemma Rinv_sqrt_pos : forall r : R, r <> 0 -> r >= 0 -> / sqrt r >= 0.
intros r H H0; try assumption.
apply Rinv_le_pos; auto.
apply non_sqrt_zero; auto.
apply sqrt_pos; auto.
Qed.
Hint Resolve non_sqrt_zero Rinv_sqrt_pos Rinv_le_pos Rmult_pos sqrt_pos
  def_sqrt: real.
 
Lemma resolution : forall x y : R, x >= 0 -> y >= 0 -> x * x = y * y -> x = y.
intros.
rewrite <- (def_sqrt x); auto with real.
rewrite <- (def_sqrt y); auto with real.
rewrite <- sqrt_mult; auto with real.
rewrite <- sqrt_mult; auto with real.
Qed.
 
Lemma inversion_sqr :
 forall x y : R, x >= 0 -> y >= 0 -> x = y * y -> y = sqrt x.
intros; symmetry  in |- *.
apply sqrt_lem_1; auto with real.
Qed.
 
Lemma sqrt_Rinv : forall x : R, x >= 0 -> x <> 0 -> sqrt (/ x) = / sqrt x.
intros.
inversion H.
replace (/ x) with (1 / x); auto with real.
rewrite sqrt_div; auto with real.
rewrite sqrt_1.
replace (1 / sqrt x) with (1 * / sqrt x); auto with real.
replace (1 / x) with (1 * / x); auto with real.
absurd (x = 0); auto.
Qed.
 
Lemma resolution2 :
 forall x y x' y' : R, x <> 0 -> x = y -> x * x' = y * y' -> x' = y'.
intros.
cut (y <> 0); intros.
replace x' with (/ x * x * x').
replace (/ x * x * x') with (/ x * (x * x')).
rewrite H1; rewrite H0.
replace (/ y * (y * y')) with (/ y * y * y').
replace (/ y * y) with 1.
ring.
auto with real.
ring.
ring.
replace (/ x * x) with 1.
ring.
auto with real.
rewrite <- H0; auto.
Qed.
 
Lemma deux_demi : 2 * / 2 = 1.
cut (2 <> 0); intros.
auto with real.
try discrR.
Qed.
Hint Resolve deux_demi: real.
 
Lemma deux_demi_a : forall a : R, a = / 2 * a + / 2 * a.
intros.
replace (/ 2 * a + / 2 * a) with (2 * / 2 * a).
replace (2 * / 2) with 1; auto with real.
ring.
Qed.
Hint Resolve deux_demi_a: real.
 
Lemma integre_not : forall a b : R, a <> 0 -> b <> 0 -> a * b <> 0.
intros.
apply Rmult_integral_contrapositive; (split; auto; try discrR).
Qed.
Hint Resolve integre_not: real.
 
Axiom lR14 : 1 + - / 2 = / 2.
Hint Resolve lR14: real.
 
Lemma lR15 : forall k : R, k * k = (1 + - k) * (1 + - k) -> k = / 2.
intros.
cut (2 <> 0); intros.
cut (2 * k = 1); intros.
replace k with (/ 2 * (2 * k)).
rewrite H1.
ring.
replace (/ 2 * (2 * k)) with (/ 2 * 2 * k).
replace (/ 2 * 2) with 1.
ring.
auto with real.
ring.
cut ((1 + - k) * (1 + - k) = - (2 * k) + (k * k + 1)); intros.
rewrite <- H in H1.
cut (2 * k = k * k + 1 + - (k * k)); intros.
rewrite H2.
ring.
pattern (k * k) at 2 in |- *.
rewrite H1.
replace (- (- (2 * k) + (k * k + 1))) with (2 * k + - (k * k + 1)).
ring.
ring.
ring.
discrR.
Qed.
Hint Resolve lR15: real.
 
Lemma lR20 : forall a : R, ~ a >= 0 -> -1 * a >= 0.
intros.
replace (-1 * a) with (- a).
cut (0 <= - a); intros.
auto with real.
apply Ropp_0_ge_le_contravar.
cut (0 > a); intros.
fourier.
apply Rfourier_not_le_gt; intros.
apply H; auto with real.
ring.
Qed.
Hint Resolve lR20: real.
 
Lemma non_produit_un : forall k k' : R, k' * k <> 1 -> 1 + - (k' * k) <> 0.
intros; red in |- *; intros.
apply H.
replace 1 with (1 + - (k' * k) + k' * k); [ idtac | ring ].
rewrite H0; ring.
Qed.
Hint Resolve non_produit_un: real.
 
Lemma opp_inv_demi_nonzero : - / 2 <> 0.
cut (-2 <> 0); intros.
replace (- / 2) with (/ -2); auto with real.
rewrite Ropp_inv_permute; auto with real.
discrR.
Qed.
Hint Resolve opp_inv_demi_nonzero: real.
 
Lemma nonzero_un : 1 <> 0.
discrR.
Qed.
 
Lemma nonzero_oppun : -1 <> 0.
discrR.
Qed.
 
Lemma nonzero_deux : 2 <> 0.
discrR.
Qed.
 
Lemma nonzero_oppdeux : -2 <> 0.
discrR.
Qed.
 
Lemma nonzero_invdeux : / 2 <> 0.
cut (2 <> 0); intros; auto with real.
discrR.
Qed.
 
Lemma nonzero_trois : 3 <> 0.
discrR.
Qed.
 
Lemma nonzero_opptrois : -3 <> 0.
discrR.
Qed.
 
Lemma nonzero_invtrois : / 3 <> 0.
cut (3 <> 0); intros; auto with real.
discrR.
Qed.
Hint Resolve nonzero_invtrois nonzero_opptrois nonzero_trois nonzero_invdeux
  nonzero_oppdeux nonzero_deux nonzero_oppun nonzero_un: real.
 
Lemma double_zero : forall a : R, 2 * a = 0 -> a = 0.
intros.
replace a with (/ 2 * (2 * a)); auto with real.
field.
Qed.
 
Lemma zero_double : forall a : R, a = 0 -> 2 * a = 0.
intuition.
Qed.
Hint Resolve double_zero zero_double: real.
 
Lemma nonzero_oppinvtrois : - / 3 <> 0.
cut (-3 <> 0); intros; auto with real.
Qed.
 
Lemma nonzero_oppinvdeux : - / 2 <> 0.
cut (-2 <> 0); intros; auto with real.
Qed.
Hint Resolve nonzero_oppinvtrois nonzero_oppinvdeux: real.
 
Lemma Rgt_inv : forall k : R, k > 0 -> / k > 0.
intros.
cut (k <> 0); intros; [ idtac | auto with real ].
cut (k >= 0); intros.
cut (/ k >= 0); intros.
2: apply Rinv_le_pos; auto.
elim H2; intros; auto.
absurd (/ k = 0); auto with real.
red in |- *.
left; try assumption.
Qed.
Hint Resolve Rgt_inv: real.
 
Definition R2 := 2.
 
Definition R4 := 2 + 2.
Hint Unfold R2 R4: real geo.
