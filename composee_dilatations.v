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


Require Export dilatations.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma compo_transl :
 forall A A' A1 I J K L : PO,
 A1 = translation I J A ->
 A' = translation K L A1 -> vec A A' = add_PP (vec I J) (vec K L).
intros A A' A1 I J K L H H0; try assumption.
cut (vec K L = vec A1 A'); intros.
cut (vec I J = vec A A1); intros.
rewrite H1; rewrite H2; Ringvec.
rewrite (translation_vecteur (I:=I) (J:=J) (A:=A) (A':=A1)); auto.
apply translation_vecteur; auto.
Qed.
 
Lemma composition_translation :
 forall A A' A1 I J K L : PO,
 A1 = translation I J A ->
 A' = translation K L A1 ->
 ex
   (fun M : PO =>
    vec I M = add_PP (vec I J) (vec K L) :>PP /\ A' = translation I M A).
intros A A' A1 I J K L H H0; try assumption.
elim
 existence_representant_som_vecteur with (A := I) (B := J) (C := K) (D := L);
 intros M H1; try clear existence_representant_som_vecteur; 
 try exact H1.
exists M.
split; [ try assumption | idtac ].
apply rec_translation_vecteur.
rewrite H1.
symmetry  in |- *; apply compo_transl with A1; auto.
Qed.
 
Lemma compo_homothetie_I :
 forall (k k' : R) (I A A' A1 : PO),
 A1 = homothetie k I A :>PO ->
 A' = homothetie k' I A1 :>PO -> A' = homothetie (k' * k) I A.
intros k k' I A A' A1 H H0; try assumption.
cut (vec I A' = mult_PP (k' * k) (vec I A)); intros.
apply vecteur_homothetie; auto.
rewrite <- mult_mult_vec.
rewrite <- (homothetie_vecteur (k:=k) (I:=I) (A:=A) (A':=A1)); auto.
apply homothetie_vecteur; auto.
Qed.
 
Lemma compo_homothetie_IJ :
 forall (k k' : R) (I J A A' A1 : PO),
 A1 = homothetie k I A :>PO ->
 A' = homothetie k' J A1 ->
 cons 1 A' =
 add_PP (add_PP (cons (k' * k) A) (cons (k' * (1 + - k)) I))
   (cons (1 + - k') J) :>PP.
unfold vec, homothetie in |- *; intros.
rewrite H0; rewrite H.
rewrite (distrib_mult_cons k (1 + - k) k' A I).
rewrite add_PP_barycentre; try discrR.
replace (k + (1 + - k)) with 1; try ring; auto.
rewrite def_mult_PP.
replace (k' * 1) with k'; try ring; auto.
rewrite add_PP_barycentre; try discrR.
replace (k' + (1 + - k')) with 1; try ring; auto.
replace (k' + (1 + - k')) with 1; try ring; try discrR.
replace (k + (1 + - k)) with 1; try ring; try discrR.
Qed.
 
Lemma compo_homothetie_IJ_1 :
 forall (k k' : R) (I J A A' A1 K : PO),
 k' * k = 1 ->
 A1 = homothetie k I A :>PO ->
 A' = homothetie k' J A1 :>PO ->
 vec I K = mult_PP (1 + - k') (vec I J) :>PP -> A' = translation I K A.
intros.
cut (vec A A' = mult_PP (1 + - k') (vec I J)); intros.
apply rec_translation_vecteur; auto.
rewrite H3; rewrite H2; auto.
cut
 (cons 1 A' =
  add_PP (add_PP (cons (k' * k) A) (cons (k' * (1 + - k)) I))
    (cons (1 + - k') J)); intros.
unfold vec in |- *.
rewrite H3; auto.
repeat rewrite add_PP_assoc.
replace (k' * (1 + - k)) with (- (k' * k) + k'); try ring; try ring; auto.
rewrite H; auto.
RingPP.
apply compo_homothetie_IJ with A1; auto.
Qed.
 
Lemma compo_homothetie_IJ_1_exists :
 forall (k : R) (I J : PO),
 k <> 0 ->
 exists K : PO,
   (forall A A' A1 : PO,
    A1 = homothetie k I A ->
    A' = homothetie (/ k) J A1 :>PO -> A' = translation I K A).
intros.
elim
 existence_representant_mult_vecteur
  with (A := I) (B := I) (C := J) (k := 1 + - / k); 
 intros K H3; try clear existence_representant_mult_vecteur.
exists K; intros.
apply compo_homothetie_IJ_1 with (2 := H0) (3 := H1); auto with *.
Qed.
 
Lemma compo_homothetie_IJ_non1 :
 forall (k k' : R) (I J A A' A1 K : PO),
 k' * k <> 1 ->
 A1 = homothetie k I A :>PO ->
 A' = homothetie k' J A1 :>PO ->
 K = barycentre (cons (k' * (1 + - k)) I) (cons (1 + - k') J) :>PO ->
 A' = homothetie (k' * k) K A.
intros; unfold homothetie in |- *.
cut (A' = barycentre (cons (k' * k) A) (cons (1 + - (k' * k)) K)); intros.
rewrite H3; auto.
elim
 cons_inj
  with
    (a := 1)
    (b := k' * k + (1 + - (k' * k)))
    (A := A')
    (B := barycentre (cons (k' * k) A) (cons (1 + - (k' * k)) K)); 
 intros; auto with *.
rewrite <- add_PP_barycentre; auto with real.
rewrite H2.
RReplace (1 + - (k' * k)) (k' * (1 + - k) + (1 + - k')).
rewrite <- add_PP_barycentre; auto with real.
rewrite add_PP_assoc.
apply compo_homothetie_IJ with A1; auto.
RReplace (k' * (1 + - k) + (1 + - k')) (1 + - (k' * k)).
auto with real.
RReplace (k' * k + (1 + - (k' * k))) 1.
auto with real.
Qed.
 
Lemma compo_homothetie_IJ_non1_exists :
 forall (k k' : R) (I J : PO),
 k' * k <> 1 ->
 exists K : PO,
   (forall A A' A1 : PO,
    A1 = homothetie k I A ->
    A' = homothetie k' J A1 :>PO -> A' = homothetie (k' * k) K A :>PO).
intros.
exists (barycentre (cons (k' * (1 + - k)) I) (cons (1 + - k') J)); intros.
apply compo_homothetie_IJ_non1 with (2 := H0) (3 := H1); auto.
Qed.
 
Lemma composee_homothetie_translation :
 forall (k : R) (A A' B B' B1 I J : PO),
 k <> 1 ->
 k <> 0 ->
 B1 = homothetie k I B :>PO ->
 B' = translation A A' B1 :>PO ->
 J =
 barycentre (cons 1 A')
   (cons (-1 + (1 + - k)) (barycentre (cons (-1) A) (cons (1 + - k) I))) :>PO ->
 B' = homothetie k J B.
unfold translation, homothetie in |- *;
 intros k A A' B B' B1 I J H H0 H1 H2 H30.
elim
 cons_inj
  with
    (a := 1)
    (b := 1)
    (A := B')
    (B := barycentre (cons k B)
            (cons (1 + - k)
               (barycentre (cons 1 A')
                  (cons (-1 + (1 + - k))
                     (barycentre (cons (-1) A) (cons (1 + - k) I))))));
 intros; auto with *.
rewrite H4; rewrite H30; auto.
rewrite H2.
pattern 1 at 1 in |- *.
replace 1 with (-1 + 2); [ idtac | try ring ].
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
pattern 1 at 3 in |- *.
replace 1 with (k + (1 + - k)); [ idtac | try ring ].
rewrite H1.
rewrite <- add_PP_barycentre; auto.
pattern 1 at 4 in |- *.
replace 1 with (k + (1 + - k)); [ idtac | try ring ].
rewrite <- add_PP_barycentre; auto.
pattern (1 + - k) at 2 in |- *.
replace (1 + - k) with (1 + (-1 + (1 + - k))); [ idtac | try ring ].
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
RingPP.
replace (-1 + (1 + - k)) with (- k); try ring; auto with *.
replace (1 + (-1 + (1 + - k))) with (1 + - k); try ring; auto with *.
replace (k + (1 + - k)) with 1; try ring; auto with *.
replace (k + (1 + - k)) with 1; try ring; auto with *.
discrR.
replace (-1 + 2) with 1; try ring; auto with *.
Qed.
 
Lemma composee_homothetie_translation_exists :
 forall (k : R) (I A A' : PO),
 k <> 1 :>R ->
 k <> 0 :>R ->
 exists J : PO,
   (forall B B' B1 : PO,
    B1 = homothetie k I B :>PO ->
    B' = translation A A' B1 :>PO -> B' = homothetie k J B :>PO).
intros.
exists
 (barycentre (cons 1 A')
    (cons (-1 + (1 + - k)) (barycentre (cons (-1) A) (cons (1 + - k) I))));
 intros.
apply composee_homothetie_translation with (4 := H2) (3 := H1); auto.
Qed.
 
Lemma composee_translation_homothetie :
 forall (k : R) (A A' B B' B1 I J : PO),
 k <> 1 ->
 k <> 0 ->
 B1 = translation A A' B :>PO ->
 B' = homothetie k I B1 :>PO ->
 J =
 barycentre (cons (- k) A)
   (cons (k + (1 + - k)) (barycentre (cons k A') (cons (1 + - k) I))) :>PO ->
 B' = homothetie k J B.
unfold translation, homothetie in |- *;
 intros k A A' B B' B1 I J H H0 H1 H2 H30.
elim
 cons_inj
  with
    (a := 1)
    (b := 1)
    (A := B')
    (B := barycentre (cons k B)
            (cons (1 + - k)
               (barycentre (cons (- k) A)
                  (cons (k + (1 + - k))
                     (barycentre (cons k A') (cons (1 + - k) I)))))); 
 intros; auto with *.
rewrite H4; rewrite H30; auto.
rewrite H2.
cut (cons k B1 = add_PP (cons (- k) A) (add_PP (cons k A') (cons k B)));
 intros.
pattern 1 at 1 in |- *.
replace 1 with (k + (1 + - k)); [ idtac | try ring ].
rewrite <- add_PP_barycentre; auto.
rewrite H3.
pattern 1 at 2 in |- *.
replace 1 with (k + (1 + - k)); [ idtac | try ring ].
rewrite <- add_PP_barycentre; auto.
pattern (1 + - k) at 2 in |- *.
replace (1 + - k) with (- k + (k + (1 + - k))); [ idtac | try ring ].
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
RingPP.
replace (k + (1 + - k)) with 1; try ring; auto with *.
replace (- k + (k + (1 + - k))) with (1 + - k); try ring; auto with *.
replace (k + (1 + - k)) with 1; try ring; auto with *.
replace (k + (1 + - k)) with 1; try ring; auto with *.
apply mult_PP_regulier with (/ k); auto with real.
replace
 (mult_PP (/ k) (add_PP (cons (- k) A) (add_PP (cons k A') (cons k B)))) with
 (add_PP (cons (-1) A) (add_PP (cons 1 A') (cons 1 B))).
replace (mult_PP (/ k) (cons k B1)) with (cons 1 B1).
rewrite H1.
pattern 1 at 1 in |- *.
replace 1 with (-1 + 2); [ idtac | try ring ].
rewrite <- add_PP_barycentre; auto with real.
rewrite <- add_PP_barycentre; auto with real.
discrR.
Fieldvec k.
Fieldvec k.
Qed.
 
Lemma composee_translation_homothetie_exists :
 forall (k : R) (I A A' : PO),
 k <> 1 :>R ->
 k <> 0 :>R ->
 exists J : PO,
   (forall B B' B1 : PO,
    B1 = translation A A' B :>PO ->
    B' = homothetie k I B1 :>PO -> B' = homothetie k J B :>PO).
intros.
exists
 (barycentre (cons (- k) A)
    (cons (k + (1 + - k)) (barycentre (cons k A') (cons (1 + - k) I))));
 intros.
apply composee_translation_homothetie with (4 := H2) (3 := H1); auto.
Qed.