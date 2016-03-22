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


Require Export formes_complexes.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma Rinv_calcul :
 forall x y : R, x <> 0 :>R -> x * y = 1 :>R -> / x = y :>R.
intros.
apply Rmult_eq_reg_l with x; auto.
rewrite H0; auto with real.
Qed.
Hint Resolve Rinv_calcul: real.
Parameter Cplus : C -> C -> C.
 
Axiom
  Cplus_def :
    forall (z1 z2 : C) (x1 y1 x2 y2 : R),
    z1 = cons_cart x1 y1 ->
    z2 = cons_cart x2 y2 -> Cplus z1 z2 = cons_cart (x1 + x2) (y1 + y2).
 
Lemma Cplus_algebrique :
 forall x1 y1 x2 y2 : R,
 Cplus (cons_cart x1 y1) (cons_cart x2 y2) = cons_cart (x1 + x2) (y1 + y2).
intros.
rewrite
 (Cplus_def (z1:=cons_cart x1 y1) (z2:=cons_cart x2 y2) (x1:=x1) (y1:=y1)
    (x2:=x2) (y2:=y2)); auto.
Qed.
Hint Resolve Cplus_algebrique: geo.
 
Lemma Cplus_commutative : forall z1 z2 : C, Cplus z1 z2 = Cplus z2 z1.
intros.
elim existence_parties_relles_imaginaires with (z := z1); intros x1 H; elim H;
 intros y1 H0; try clear H; try exact H0.
elim existence_parties_relles_imaginaires with (z := z2); intros x2 H; elim H;
 intros y2 H1; try clear H; try exact H1.
rewrite (Cplus_def (z1:=z1) (z2:=z2) (x1:=x1) (y1:=y1) (x2:=x2) (y2:=y2));
 auto.
rewrite (Cplus_def (z1:=z2) (z2:=z1) (x1:=x2) (y1:=y2) (x2:=x1) (y2:=y1));
 auto.
replace (x1 + x2) with (x2 + x1); [ idtac | ring ].
replace (y1 + y2) with (y2 + y1); [ auto | ring ].
Qed.
 
Lemma Cplus_z_zeroC : forall z : C, Cplus z zeroC = z.
intros.
elim existence_parties_relles_imaginaires with (z := z); intros x1 H; elim H;
 intros y1 H0; try clear H; try exact H0.
rewrite (Cplus_def (z1:=z) (z2:=zeroC) (x1:=x1) (y1:=y1) (x2:=0) (y2:=0));
 auto.
replace (x1 + 0) with x1; [ idtac | ring ].
replace (y1 + 0) with y1; [ auto | ring ].
Qed.
 
Lemma Cplus_associative :
 forall z1 z2 z3 : C, Cplus z1 (Cplus z2 z3) = Cplus (Cplus z1 z2) z3.
intros.
elim existence_parties_relles_imaginaires with (z := z1); intros x1 H; elim H;
 intros y1 H0; try clear H; try exact H0.
elim existence_parties_relles_imaginaires with (z := z2); intros x2 H; elim H;
 intros y2 H1; try clear H; try exact H1.
elim existence_parties_relles_imaginaires with (z := z3); intros x3 H; elim H;
 intros y3 H2; try clear H; try exact H2.
rewrite (Cplus_def (z1:=z1) (z2:=z2) (x1:=x1) (y1:=y1) (x2:=x2) (y2:=y2));
 auto.
rewrite
 (Cplus_def (z1:=cons_cart (x1 + x2) (y1 + y2)) (z2:=z3) (x1:=
    x1 + x2) (y1:=y1 + y2) (x2:=x3) (y2:=y3)); auto.
rewrite (Cplus_def (z1:=z2) (z2:=z3) (x1:=x2) (y1:=y2) (x2:=x3) (y2:=y3));
 auto.
rewrite
 (Cplus_def (z1:=z1) (z2:=cons_cart (x2 + x3) (y2 + y3)) (x1:=x1) (y1:=y1)
    (x2:=x2 + x3) (y2:=y2 + y3)); auto.
replace (x1 + (x2 + x3)) with (x1 + x2 + x3); [ idtac | ring ].
replace (y1 + (y2 + y3)) with (y1 + y2 + y3); [ auto | ring ].
Qed.
Parameter Copp : C -> C.

Definition Cminus x y := Cplus x (Copp y). 

Axiom
  Copp_def :
    forall (z : C) (x y : R),
    z = cons_cart x y -> Copp z = cons_cart (- x) (- y).
 
Lemma Copp_algebrique :
 forall x y : R, Copp (cons_cart x y) = cons_cart (- x) (- y).
intros.
rewrite (Copp_def (z:=cons_cart x y) (x:=x) (y:=y)); auto.
Qed.
 
Lemma Cplus_z_oppz : forall z : C, Cplus z (Copp z) = zeroC.
intros.
elim existence_parties_relles_imaginaires with (z := z); intros x1 H; elim H;
 intros y1 H0; try clear H; try exact H0.
unfold zeroC in |- *; rewrite H0; rewrite Copp_algebrique;
 rewrite Cplus_algebrique.
replace (x1 + - x1) with 0; [ idtac | ring ].
replace (y1 + - y1) with 0; [ auto | ring ].
Qed.
Hint Resolve Cplus_z_oppz Copp_algebrique Cplus_commutative Cplus_z_zeroC:
  geo.
Parameter Cmult : C -> C -> C.
 
Axiom
  Cmult_module : forall z z' : C, module (Cmult z z') = module z * module z'.
 
Axiom
  Cmult_argument :
    forall z z' : C,
    z <> zeroC ->
    z' <> zeroC -> argument (Cmult z z') = plus (argument z) (argument z').
 
Lemma Cmult_zeroC_z : forall z : C, Cmult zeroC z = zeroC.
intros.
apply module_nul_zeroC.
rewrite Cmult_module; rewrite module_zeroC; ring.
Qed.
 
Lemma Cmult_z_zeroC : forall z : C, Cmult z zeroC = zeroC.
intros.
apply module_nul_zeroC.
rewrite Cmult_module; rewrite module_zeroC; ring.
Qed.
 
Lemma nonzero_produit :
 forall z z' : C, z <> zeroC -> z' <> zeroC -> Cmult z z' <> zeroC.
intros.
apply nonzero_module.
rewrite Cmult_module.
apply Rmult_integral_contrapositive.
split; auto with geo.
Qed.
Hint Resolve Cmult_module Cmult_argument nonzero_produit Cmult_z_zeroC
  Cmult_zeroC_z: geo.
 
Lemma Cmult_z_z' :
 forall (z z' : C) (r a r' a' : R),
 z <> zeroC ->
 z' <> zeroC ->
 z = cons_pol r a ->
 z' = cons_pol r' a' -> Cmult z z' = cons_pol (r * r') (a + a').
intros.
apply forme_polaire_def; auto with geo.
rewrite Cmult_module.
rewrite (complexe_pol_module (z:=z) (r:=r) (a:=a)); auto with geo.
rewrite (complexe_pol_module (z:=z') (r:=r') (a:=a')); auto with geo.
rewrite Cmult_argument; auto with geo.
rewrite (complexe_pol_argument (z:=z) (r:=r) (a:=a)); auto with geo.
rewrite (complexe_pol_argument (z:=z') (r:=r') (a:=a')); auto with geo.
Qed.
Hint Resolve Cmult_z_z': geo.
 
Lemma Cmult_commutative : forall z z' : C, Cmult z z' = Cmult z' z.
intros.
elim (classic (z = zeroC)); intros.
rewrite H; rewrite Cmult_zeroC_z; rewrite Cmult_z_zeroC; auto.
elim (classic (z' = zeroC)); intros.
rewrite H0; rewrite Cmult_zeroC_z; rewrite Cmult_z_zeroC; auto.
elim existence_forme_polaire with (z := z);
 [ intros r H1; elim H1; intros a H2; elim H2; intros H3 H4;
    try clear H2 H1 existence_forme_polaire; try exact H3
 | auto with geo ].
elim existence_forme_polaire with (z := z');
 [ intros r' H5; elim H5; intros a' H6; elim H6; intros H7 H8;
    try clear H6 H5 existence_forme_polaire; try exact H7
 | auto with geo ].
rewrite (Cmult_z_z' (z:=z) (z':=z') (r:=r) (a:=a) (r':=r') (a':=a'));
 auto with geo.
rewrite (Cmult_z_z' (z:=z') (z':=z) (r:=r') (a:=a') (r':=r) (a':=a));
 auto with geo.
replace (r * r') with (r' * r); [ idtac | ring ].
replace (a + a') with (a' + a); [ auto | ring ].
Qed.
 
Lemma Cmult_associative :
 forall z1 z2 z3 : C, Cmult z1 (Cmult z2 z3) = Cmult (Cmult z1 z2) z3.
intros.
elim (classic (z1 = zeroC)); intros.
rewrite H.
repeat rewrite Cmult_zeroC_z; auto.
elim (classic (z2 = zeroC)); intros.
rewrite H0.
repeat rewrite Cmult_zeroC_z; repeat rewrite Cmult_z_zeroC;
 repeat rewrite Cmult_zeroC_z; auto.
elim (classic (z3 = zeroC)); intros.
rewrite H1.
repeat rewrite Cmult_z_zeroC; auto.
apply egalite_forme_polaire.
apply nonzero_produit; auto with geo.
apply nonzero_produit; auto with geo.
repeat rewrite Cmult_module; ring.
repeat rewrite Cmult_argument; auto with geo.
elim existence_argument with (z := z1);
 [ intros a H2; try clear existence_argument; try exact H2 | auto with geo ].
elim existence_argument with (z := z2);
 [ intros a0 H3; try clear existence_argument; try exact H3 | auto with geo ].
elim existence_argument with (z := z3);
 [ intros a1 H4; try clear existence_argument; try exact H4 | auto with geo ].
rewrite H2; rewrite H3; rewrite H4.
repeat rewrite <- add_mes_compatible.
replace (a + (a0 + a1)) with (a + a0 + a1); [ auto | ring ].
Qed.
 
Lemma Cmult_z_oneC : forall z : C, Cmult z oneC = z.
intros.
elim (classic (z = zeroC)); intros.
rewrite H.
repeat rewrite Cmult_zeroC_z; auto with geo.
apply egalite_forme_polaire; auto with geo.
rewrite Cmult_module; rewrite module_oneC; ring.
repeat rewrite Cmult_argument; auto with geo.
rewrite argument_oneC; auto with geo.
Qed.
 
Definition Csqr (z : C) := Cmult z z.
Hint Unfold Csqr: geo.
 
Lemma i_carre : Csqr i = Rinj (-1).
unfold Csqr in |- *.
apply egalite_forme_polaire; auto with geo.
rewrite Cmult_module; rewrite module_opp_un; rewrite module_i; ring.
repeat rewrite Cmult_argument; auto with geo.
rewrite argument_opp_un; rewrite argument_i.
rewrite <- add_mes_compatible; auto.
Qed.
 
Theorem Cmult_algebrique :
 forall x1 y1 x2 y2 : R,
 Cmult (cons_cart x1 y1) (cons_cart x2 y2) =
 cons_cart (x1 * x2 + - (y1 * y2)) (y1 * x2 + x1 * y2).
intros.
elim (classic (cons_cart x1 y1 = zeroC)); intros.
elim algebrique_zeroC with (a := x1) (b := y1);
 [ intros; try exact H1 | auto ].
rewrite H1; rewrite H0.
replace (0 * x2 + - (0 * y2)) with 0; [ idtac | ring ].
replace (0 * x2 + 0 * y2) with 0; [ idtac | ring ].
repeat rewrite Cmult_zeroC_z; auto.
elim (classic (cons_cart x2 y2 = zeroC)); intros.
elim algebrique_zeroC with (a := x2) (b := y2);
 [ intros; try exact H1 | auto ].
rewrite H1; rewrite H2.
replace (x1 * 0 + - (y1 * 0)) with 0; [ idtac | ring ].
replace (y1 * 0 + x1 * 0) with 0; [ idtac | ring ].
repeat rewrite Cmult_z_zeroC; auto.
elim existence_forme_polaire with (z := cons_cart x1 y1);
 [ intros r1 H1; elim H1; intros a1 H2; elim H2; intros H3 H4;
    try clear H2 H1; try exact H4
 | auto with geo ].
elim existence_forme_polaire with (z := cons_cart x2 y2);
 [ intros r2 H1; elim H1; intros a2 H2; elim H2; intros H5 H6;
    try clear H2 H1; try exact H6
 | auto with geo ].
generalize (Cmult_module (cons_cart x1 y1) (cons_cart x2 y2)); intros.
rewrite H5 in H1; rewrite H3 in H1.
lapply (Cmult_argument (z:=cons_cart x1 y1) (z':=cons_cart x2 y2)); intros;
 auto with geo.
rewrite H4 in H2; rewrite H6 in H2.
cut
 (Cmult (cons_cart x1 y1) (cons_cart x2 y2) = cons_pol (r1 * r2) (a1 + a2));
 intros.
rewrite
 (polaire_calcul_algebrique (z:=Cmult (cons_cart x1 y1) (cons_cart x2 y2))
    (r:=r1 * r2) (a:=a1 + a2)); auto with geo.
elim
 passage_polaire_algebrique
  with (z := cons_cart x1 y1) (r := r1) (a := a1) (x := x1) (y := y1);
 [ intros; try exact H8 | auto with geo | auto with geo | auto with geo ].
rewrite H8; rewrite H9.
elim
 passage_polaire_algebrique
  with (z := cons_cart x2 y2) (r := r2) (a := a2) (x := x2) (y := y2);
 [ intros | auto with geo | auto with geo | auto with geo ].
rewrite H10; rewrite H11.
rewrite cos_som; rewrite sin_som.
replace (r1 * r2 * (cos a1 * cos a2 + - (sin a1 * sin a2))) with
 (r1 * cos a1 * (r2 * cos a2) + - (r1 * sin a1 * (r2 * sin a2)));
 [ idtac | ring ].
replace (r1 * r2 * (sin a1 * cos a2 + sin a2 * cos a1)) with
 (r1 * sin a1 * (r2 * cos a2) + r1 * cos a1 * (r2 * sin a2)); 
 [ auto | ring ].
apply forme_polaire_def; auto with geo.
rewrite H2; auto.
rewrite <- add_mes_compatible; auto.
Qed.
Hint Resolve Cmult_algebrique: geo.
 
Theorem Cmult_distributive :
 forall z1 z2 z3 : C,
 Cmult z1 (Cplus z2 z3) = Cplus (Cmult z1 z2) (Cmult z1 z3).
intros.
elim existence_parties_relles_imaginaires with (z := z1); intros a1 H; elim H;
 intros b1 H0; try clear H; try exact H0.
elim existence_parties_relles_imaginaires with (z := z2); intros a2 H; elim H;
 intros b2 H1; try clear H; try exact H1.
elim existence_parties_relles_imaginaires with (z := z3); intros a3 H; elim H;
 intros b3 H2; try clear H; try exact H2.
rewrite H2; rewrite H1; rewrite H0.
repeat rewrite Cmult_algebrique; repeat rewrite Cplus_algebrique;
 repeat rewrite Cmult_algebrique.
replace (a1 * (a2 + a3) + - (b1 * (b2 + b3))) with
 (a1 * a2 + - (b1 * b2) + (a1 * a3 + - (b1 * b3))); 
 [ idtac | ring ].
replace (b1 * (a2 + a3) + a1 * (b2 + b3)) with
 (b1 * a2 + a1 * b2 + (b1 * a3 + a1 * b3)); [ auto | ring ].
Qed.
 
Lemma Cplus_zeroC_z : forall z : C, Cplus zeroC z = z.
intros.
rewrite Cplus_commutative; auto with geo.
Qed.
Hint Resolve Cmult_z_oneC: geo.
 
Lemma Cmult_oneC_z : forall z : C, Cmult oneC z = z.
intros.
rewrite Cmult_commutative; auto with geo.
Qed.
 
Lemma Cmult_distributive_r :
 forall z1 z2 z3 : C,
 Cmult (Cplus z1 z2) z3 = Cplus (Cmult z1 z3) (Cmult z2 z3).
intros.
rewrite Cmult_commutative; rewrite Cmult_distributive.
rewrite Cmult_commutative; rewrite (Cmult_commutative z3 z2); auto with geo.
Qed.
 
Lemma CTheory :
 ring_theory zeroC oneC Cplus Cmult Cminus Copp (eq(A:=C)).
split.
exact Cplus_zeroC_z.
exact Cplus_commutative.
exact Cplus_associative.
exact Cmult_oneC_z.
exact Cmult_commutative.
exact Cmult_associative.
exact Cmult_distributive_r.
reflexivity.
exact Cplus_z_oppz.
Defined.
Add Ring Cring : CTheory.
 
Lemma algebrique_operations :
 forall x y : R, cons_cart x y = Cplus (Rinj x) (Cmult i (Rinj y)).
unfold i in |- *; unfold Rinj in |- *; intros.
rewrite Cmult_algebrique; rewrite Cplus_algebrique.
replace (x + (0 * y + - (1 * 0))) with x; [ idtac | ring ].
replace (0 + (1 * y + 0 * 0)) with y; [ auto | ring ].
Qed.
 
Lemma existence_inverse :
 forall z : C, z <> zeroC -> exists z' : C, Cmult z z' = oneC.
intros.
elim existence_forme_polaire with (z := z);
 [ intros r H1; elim H1; intros a H2; elim H2; intros H3 H4; try clear H2 H1;
    try exact H3
 | auto with geo ].
cut (r <> 0); intros.
cut (/ r <> 0); intros; auto with real.
cut (cons_pol (/ r) (- a) <> zeroC); intros.
exists (cons_pol (/ r) (- a)).
apply egalite_forme_polaire; auto with geo.
rewrite Cmult_module; rewrite module_oneC; rewrite complexe_polaire_module;
 rewrite H3; field; trivial.
rewrite Cmult_argument; auto with geo.
rewrite complexe_polaire_argument; auto with geo.
rewrite H4; rewrite argument_oneC.
rewrite <- add_mes_compatible.
replace (a + - a) with 0; [ auto | ring ].
auto with real geo.
rewrite <- H3; auto with geo.
Qed.
 
Lemma unicite_inverse :
 forall z z1 z2 : C,
 z <> zeroC -> Cmult z z1 = oneC -> Cmult z z2 = oneC -> z1 = z2.
intros.
cut (module z * module z1 = 1); intros.
cut (module z * module z2 = 1); intros.
cut (module z <> 0); intros; auto with geo.
cut (module z1 <> 0); intros.
cut (module z2 <> 0); intros.
cut (z1 <> zeroC); intros; auto with geo.
cut (z2 <> zeroC); intros; auto with geo.
apply egalite_forme_polaire; auto with geo.
replace (module z1) with (/ module z); auto with real.
auto with real.
cut (plus (argument z) (argument z1) = image_angle 0); intros.
cut (plus (argument z) (argument z2) = image_angle 0); intros.
rewrite (opp_angle (a:=argument z) (b:=argument z1)); auto.
rewrite (opp_angle (a:=argument z) (b:=argument z2)); auto.
rewrite <- Cmult_argument; auto with geo.
rewrite H1; rewrite <- argument_oneC; auto.
rewrite <- Cmult_argument; auto with geo.
rewrite H0; rewrite <- argument_oneC; auto.
cut (module z * module z2 <> 0); intros.
red in |- *; intros; apply H6.
rewrite H7; ring.
rewrite H3; discrR.
cut (module z * module z1 <> 0); intros.
red in |- *; intros; apply H5.
rewrite H6; ring.
rewrite H2; discrR.
rewrite <- Cmult_module; rewrite H1; rewrite <- module_oneC; auto.
rewrite <- Cmult_module; rewrite H0; rewrite <- module_oneC; auto.
Qed.
Parameter Cinv : C -> C.
 
Axiom Cinv_def : forall z : C, z <> zeroC -> Cmult z (Cinv z) = oneC.
 
Axiom
  Cinv_def2 : forall z z' : C, z <> zeroC -> Cmult z z' = oneC -> Cinv z = z'.
 
Lemma Cinv_l : forall z : C, z <> zeroC -> Cmult (Cinv z) z = oneC.
intros.
rewrite <- (Cinv_def (z:=z)); auto.
ring.
Qed.
Hint Resolve Cinv_def Cinv_def2 Cinv_l: geo.
 
Lemma Cinv_module : forall z : C, z <> zeroC -> module (Cinv z) = / module z.
intros.
cut (module z * module (Cinv z) = 1); intros.
cut (module z <> 0); intros; auto with geo.
apply Rmult_eq_reg_l with (module z); auto.
rewrite H0; auto with real.
rewrite <- Cmult_module; rewrite Cinv_def; auto with geo.
Qed.
Hint Resolve Cinv_module: geo.
 
Lemma inv_nonzero : forall z : C, z <> zeroC -> Cinv z <> zeroC.
intros.
apply nonzero_module.
rewrite Cinv_module; auto with geo.
cut (module z <> 0); intros; auto with geo.
auto with real.
Qed.
Hint Resolve inv_nonzero: geo.
 
Lemma Cinv_argument :
 forall z : C, z <> zeroC -> argument (Cinv z) = opp (argument z).
intros.
cut (Cinv z <> zeroC); intros; auto with geo.
cut (plus (argument z) (argument (Cinv z)) = image_angle 0); intros.
apply opp_angle; auto.
rewrite <- argument_oneC.
rewrite <- Cmult_argument; auto with geo.
rewrite Cinv_def; auto with geo.
Qed.
Hint Resolve Cinv_argument: geo.
Parameter Cdiv : C -> C -> C.
 
Axiom
  Cdiv_def : forall z z' : C, z' <> zeroC -> Cdiv z z' = Cmult z (Cinv z').
 
Lemma Cdiv_module :
 forall z z' : C, z' <> zeroC -> module (Cdiv z z') = module z * / module z'.
intros.
rewrite Cdiv_def; auto with geo.
rewrite Cmult_module; rewrite Cinv_module; auto.
Qed.
Hint Resolve Cdiv_module: geo.
 
Lemma Cdiv_argument :
 forall z z' : C,
 z <> zeroC ->
 z' <> zeroC -> argument (Cdiv z z') = plus (argument z) (opp (argument z')).
intros.
rewrite Cdiv_def; auto with geo.
rewrite Cmult_argument; auto with geo.
rewrite Cinv_argument; auto with geo.
Qed.
Hint Resolve Cdiv_argument: geo.
 
Lemma Cintegre :
 forall z z' : C, z <> zeroC -> Cmult z z' = zeroC -> z' = zeroC.
intros.
replace z' with (Cmult (Cmult (Cinv z) z) z')
  by (rewrite Cinv_l; trivial; ring).
replace (Cmult (Cmult (Cinv z) z) z') with (Cmult (Cinv z) (Cmult z z'))
  by ring.
rewrite H0; ring.
Qed.
 
Lemma module_un_nonzero : forall a : R, cons_pol 1 a <> zeroC.
intros.
apply polaire_non_nul; try discrR.
Qed.
Hint Resolve module_un_nonzero: geo.
 
Lemma module_un_trivial : forall a : R, module (cons_pol 1 a) = 1.
intros; auto with geo.
Qed.
 
Lemma argument_module_un :
 forall a : R, argument (cons_pol 1 a) = image_angle a.
intros.
rewrite (complexe_polaire_argument (r:=1) a); intros; auto with geo.
discrR.
Qed.
 
Lemma polaire_produit :
 forall r a : R, r <> 0 -> cons_pol r a = Cmult (Rinj r) (cons_pol 1 a).
intros.
apply egalite_forme_polaire; auto with geo.
rewrite Cmult_module; rewrite module_un_trivial; rewrite module_reel;
  ring_simplify.
pattern r at 2 in |- *.
rewrite <- (complexe_polaire_module r a); auto with geo.
rewrite Cmult_argument; auto with geo.
rewrite argument_module_un.
rewrite argument_reel_pos; auto with geo.
rewrite complexe_polaire_argument; auto with geo.
rewrite plus_commutative; auto with geo.
cut (r >= 0); intros.
change (r > 0) in |- *.
elim H0; intros; auto.
absurd (r = 0); auto.
rewrite <- (complexe_polaire_module r a); auto with geo.
Qed.
 
Lemma affixe_vec_AB :
 forall (a b : C) (A B : PO),
 a = affixe A -> b = affixe B -> Cplus b (Copp a) = affixe_vec (vec A B).
intros.
elim existence_parties_relles_imaginaires with (z := a); intros a1 H2;
 elim H2; intros a2 H3; try clear H2; try exact H3.
elim existence_parties_relles_imaginaires with (z := b); intros b1 H4;
 elim H4; intros b2 H5; try clear H4; try exact H5.
elim
 cartvec_AB
  with
    (a1 := a1)
    (a2 := a2)
    (b1 := b1)
    (b2 := b2)
    (O := O)
    (I := I)
    (J := J)
    (A := A)
    (B := B);
 [ intros H1 H2; try clear cartvec_AB; try exact H2
 | eauto with geo
 | eauto with geo
 | eauto with geo
 | eauto with geo
 | eauto with geo ].
rewrite H5; rewrite H3; rewrite Copp_algebrique; rewrite Cplus_algebrique.
rewrite (absvec_ordvec_affixe (a:=b1 + - a1) (b:=b2 + - a2) (A:=A) (B:=B));
 auto.
Qed.
 
Lemma affixe_vec_AB_affixes :
 forall A B : PO, affixe_vec (vec A B) = Cplus (affixe B) (Copp (affixe A)).
intros.
elim existence_affixe_point with (M := A); intros a H; try exact H.
elim existence_affixe_point with (M := B); intros b; intros.
symmetry  in |- *; rewrite <- H; rewrite <- H0.
apply affixe_vec_AB; auto.
Qed.
Hint Resolve egalite_vecteur_distance: geo.
 
Lemma module_difference :
 forall (a b : C) (A B : PO),
 a = affixe A -> b = affixe B -> module (Cplus b (Copp a)) = distance A B.
intros.
cut (Cplus b (Copp a) = affixe_vec (vec A B)); intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 intros D H2; intros; try exact H2.
cut (Cplus b (Copp a) = affixe D); intros.
rewrite (module_def (z:=Cplus b (Copp a)) (M:=D)); auto with geo.
cut (Cplus b (Copp a) = affixe_vec (vec O D)); intros; auto with geo.
rewrite H1; rewrite H2; auto.
apply affixe_vec_AB; auto.
Qed.
 
Lemma argument_difference :
 forall (a b : C) (A B : PO),
 A <> B ->
 a = affixe A ->
 b = affixe B -> argument (Cplus b (Copp a)) = cons_AV (vec O I) (vec A B).
intros.
cut (Cplus b (Copp a) = affixe_vec (vec A B)); intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B); intros D;
 intros.
cut (Cplus b (Copp a) = affixe D); intros.
rewrite (argument_def (M:=D) (z:=Cplus b (Copp a))); auto with geo.
rewrite H3; auto.
red in |- *; intros; apply H.
apply vecteur_nul_conf.
rewrite <- H3; rewrite <- H5; Ringvec.
cut (Cplus b (Copp a) = affixe_vec (vec O D)); intros; auto with geo.
rewrite H2; rewrite H3; auto with geo.
apply affixe_vec_AB; auto.
Qed.
Hint Resolve module_difference argument_difference: geo.
 
Lemma diff_nonzero :
 forall (a b : C) (A B : PO),
 a = affixe A -> b = affixe B -> A <> B :>PO -> Cplus b (Copp a) <> zeroC.
intros.
apply nonzero_module.
rewrite (module_difference (a:=a) (b:=b) (A:=A) (B:=B)); auto with geo.
Qed.
Hint Resolve diff_nonzero: geo.
 
Lemma module_quotient :
 forall (a b d e : C) (A B D E : PO),
 D <> E :>PO ->
 a = affixe A ->
 b = affixe B ->
 d = affixe D ->
 e = affixe E ->
 module (Cdiv (Cplus b (Copp a)) (Cplus e (Copp d))) =
 distance A B * / distance D E.
intros.
rewrite Cdiv_def.
rewrite Cmult_module; rewrite Cinv_module; auto with geo.
rewrite (module_difference (a:=a) (b:=b) (A:=A) (B:=B)); auto with geo.
rewrite (module_difference (a:=d) (b:=e) (A:=D) (B:=E)); auto with geo.
apply diff_nonzero with (3 := H); auto.
apply diff_nonzero with (3 := H); auto.
Qed.
Hint Resolve module_quotient Chasles_diff: geo.
 
Lemma argument_quotient :
 forall (a b d e : C) (A B D E : PO),
 A <> B :>PO ->
 D <> E :>PO ->
 a = affixe A ->
 b = affixe B ->
 d = affixe D ->
 e = affixe E ->
 argument (Cdiv (Cplus b (Copp a)) (Cplus e (Copp d))) =
 cons_AV (vec D E) (vec A B).
intros.
cut (Cplus b (Copp a) <> zeroC); intros.
cut (Cplus e (Copp d) <> zeroC); intros.
rewrite Cdiv_def; auto with geo.
rewrite Cmult_argument; auto with geo.
rewrite Cinv_argument; auto with geo.
rewrite (argument_difference (a:=a) (b:=b) (A:=A) (B:=B)); auto with geo.
rewrite (argument_difference (a:=d) (b:=e) (A:=D) (B:=E)); auto with geo.
apply diff_nonzero with (3 := H0); auto.
apply diff_nonzero with (3 := H); auto.
Qed.
