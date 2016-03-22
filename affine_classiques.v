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
 
Lemma triangle_droite_milieu_paralleles :
 forall A B C A' B' : PO,
 triangle A B C ->
 A' = milieu B C :>PO ->
 B' = milieu A C :>PO -> paralleles (droite A B) (droite A' B').
intros A B C A' B' H H0 H1; try assumption.
deroule_triangle A B C.
apply colineaires_paralleles with (-2); auto.
apply (deux_milieux_distincts (A:=B) (B:=C) (C:=A)); auto with geo.
rewrite <- (droite_milieu (A:=C) (B:=A) (C:=B) (I:=B') (J:=A'));
 auto with geo.
Ringvec.
Qed.
 
Lemma milieu_parallelogrammme :
 forall A B C D I : PO, vec A B = vec D C -> I = milieu A C -> I = milieu B D.
unfold vec in |- *; intros.
elim cons_inj with (a := 2) (b := 2) (A := I) (B := milieu B D); intros; auto;
 try discrR.
rewrite <- add_PP_milieu.
rewrite H0.
rewrite <- add_PP_milieu.
RingPP2 H.
RingPP.
Qed.
 
Lemma milieu_parallelogrammme_rec:
 forall (A B C D I : PO), I = milieu A C -> I = milieu B D ->  vec A B = vec D C.
unfold vec; intros.
assert (add_PP (cons 1 B) (cons 1 D) = add_PP (cons 1 A) (cons 1 C)).
repeat rewrite add_PP_milieu.
rewrite <- H.
rewrite <- H0; auto.
RingPP1 H1.
RingPP.
Qed.

Lemma caract_milieu_parallelogramme:
 forall (A B C D : PO),  (milieu A C = milieu B D <-> parallelogramme A B C D).
intros.
elim (existence_milieu A C); [intros I H; (try clear existence_milieu)].
rewrite <- H.
unfold parallelogramme; split; intros.
apply milieu_parallelogrammme_rec with I; auto.
eapply milieu_parallelogrammme;eauto.
Qed.

Lemma Thales_PP :
 forall A B C D : PO,
 A <> C ->
 B <> D ->
 paralleles (droite A C) (droite B D) ->
 exists k : R,
   add_PP (cons 1 A) (cons k B) = add_PP (cons 1 C) (cons k D) :>PP.
intros A B C D H10 H11 H; try assumption.
elim def_paralleles2 with (3 := H); auto.
intros k H2.
exists (- k).
RingPP1 H2.
RingPP.
Qed.
 
Lemma reciproque_Thales_PP :
 forall (A B C D : PO) (k : R),
 A <> C :>PO ->
 B <> D :>PO ->
 add_PP (cons 1 A) (cons k B) = add_PP (cons 1 C) (cons k D) ->
 paralleles (droite A C) (droite B D).
intros A B C D k H10 H11 H; try assumption.
apply def_paralleles with (- k); auto.
replace (- - k) with k; try ring.
RingPP2 H.
RingPP.
Qed.
 
Theorem Thales_expl :
 forall A B C D : PO,
 A <> C :>PO ->
 B <> D :>PO ->
 paralleles (droite A C) (droite B D) ->
 vec B A = vec D C \/
 (exists k : R,
    (exists I : PO,
       vec I A = mult_PP k (vec I B) /\ vec I C = mult_PP k (vec I D))).
intros A B C D H11 H10 H; try assumption.
elim Thales_PP with (3 := H); auto.
intros k H2.
elim (classic (k = -1)); intros H3.
unfold vec in |- *; left.
rewrite <- H3; auto.
rewrite add_PP_sym; auto.
rewrite H2; auto.
Ringvec.
right; try assumption.
exists (- k).
exists (barycentre (cons 1 A) (cons k B)).
split; [ try assumption | idtac ].
apply
 add_PP_vec_reg
  with (a := k) (A := barycentre (cons 1 A) (cons k B)) (B := B).
rewrite add_PP_sym; auto.
rewrite <- mult_1_vec; auto.
rewrite def_vecteur_bary; auto.
Ringvec.
unfold not in |- *; intros; apply H3.
replace (-1) with (-1 + (1 + k)).
try ring.
rewrite H0; try ring.
cut (barycentre (cons 1 A) (cons k B) = barycentre (cons 1 C) (cons k D));
 intros.
rewrite H0; try ring.
apply
 add_PP_vec_reg
  with (a := k) (A := barycentre (cons 1 C) (cons k D)) (B := D).
rewrite add_PP_sym; auto.
rewrite <- mult_1_vec; auto.
rewrite def_vecteur_bary; auto.
Ringvec.
unfold not in |- *; intros; apply H3.
replace (-1) with (-1 + (1 + k)).
try ring.
rewrite H1; try ring.
elim
 cons_inj
  with
    (a := 1 + k)
    (b := 1 + k)
    (A := barycentre (cons 1 A) (cons k B))
    (B := barycentre (cons 1 C) (cons k D)); (intros; auto).
repeat rewrite <- add_PP_barycentre; auto.
unfold not in |- *; intros; apply H3.
replace (-1) with (-1 + (1 + k)).
try ring.
rewrite H0; try ring.
unfold not in |- *; intros; apply H3.
replace (-1) with (-1 + (1 + k)).
try ring.
rewrite H0; try ring.
unfold not in |- *; intros; apply H3.
replace (-1) with (-1 + (1 + k)).
try ring.
rewrite H0; try ring.
Qed.
 
Theorem reciproque_Thales_expl :
 forall (A B C D I : PO) (k : R),
 A <> C :>PO ->
 B <> D :>PO ->
 vec I A = mult_PP k (vec I B) :>PP ->
 vec I C = mult_PP k (vec I D) :>PP -> paralleles (droite A C) (droite B D).
unfold vec in |- *; intros A B C D I k H10 H11 H H0.
apply reciproque_Thales_PP with (- k); auto.
RingPP2 H.
RingPP2 H0.
RingPP.
Qed.
 
Lemma trapeze_complet_PP :
 forall A B C D I J : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) ->
 I = milieu C D ->
 J = milieu A B ->
 ex
   (fun k : R =>
    add_PP (cons 1 A) (cons k C) = add_PP (cons 1 B) (cons k D) :>PP /\
    add_PP (cons 1 A) (cons k C) = add_PP (cons 1 J) (cons k I) :>PP).
intros A B C D I J H10 H11 H H0 H1; try assumption.
elim Thales_PP with (3 := H); auto.
intros x H2; try assumption.
exists x.
split; [ try assumption | idtac ].
rewrite H1; rewrite H0.
apply mult_PP_regulier with (k := 2); try discrR.
repeat rewrite <- distrib_mult_cons.
replace (2 * 1) with 2; try ring; auto.
rewrite <- add_PP_milieu.
replace (2 * x) with (x * 2); try ring; auto.
repeat rewrite <- def_mult_PP.
rewrite <- add_PP_milieu.
repeat rewrite <- add_PP_A.
RingPP1 H2.
RingPP.
Qed.
 
Lemma trapeze_complet_expl :
 forall A B C D I J : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) ->
 I = milieu C D ->
 J = milieu A B ->
 vec C A = vec D B /\ vec C A = vec I J \/ concours_3 A C B D J I.
intros A B C D I J H10 H11 H H0 H1; try assumption.
unfold concours_3, vec in |- *; intros.
elim
 trapeze_complet_PP
  with (A := A) (B := B) (C := C) (D := D) (I := I) (J := J);
 [ intros k H2 | auto | auto | auto | auto | auto ].
elim H2; intros H3 H4; try clear H2; try exact H3.
elim (classic (k = -1)); intros.
rewrite H2 in H3.
rewrite H2 in H4.
left; try assumption.
split; [ try assumption | idtac ].
RingPP1 H3; RingPP.
RingPP1 H4; RingPP.
right; try assumption.
cut (1 + k <> 0); intros.
rewrite add_PP_barycentre in H4; auto.
rewrite add_PP_barycentre in H4; auto.
rewrite add_PP_barycentre in H3; auto.
rewrite add_PP_barycentre in H3; auto.
exists (barycentre (cons 1 A) (cons k C)).
split; [ apply barycentre_alignes; auto | idtac ].
split; [ try assumption | idtac ].
replace (barycentre (cons 1 A) (cons k C)) with
 (barycentre (cons 1 B) (cons k D)).
apply barycentre_alignes; auto.
apply conversion_PP with (a := 1 + k) (b := 1 + k); auto.
replace (barycentre (cons 1 A) (cons k C)) with
 (barycentre (cons 1 J) (cons k I)).
apply barycentre_alignes; auto.
apply conversion_PP with (a := 1 + k) (b := 1 + k); auto.
unfold not in |- *; intros; apply H2.
replace k with (-1 + (1 + k)).
rewrite H5; ring.
ring.
Qed.
Hint Immediate paralleles_ABBA paralleles_sym: geo.
 
Lemma trapeze_complet_expl2 :
 forall A B C D I J : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) ->
 I = milieu C D ->
 J = milieu A B ->
 vec D A = vec C B /\ vec D A = vec I J \/ concours_3 A D B C J I.
intros.
elim (trapeze_complet_expl (A:=A) (B:=B) (C:=D) (D:=C) (I:=I) (J:=J));
 auto with geo; intros.
apply paralleles_trans with (C := C) (D := D); auto with geo.
Qed.
 
Theorem Desargues :
 forall A B C A1 B1 C1 S : PO,
 C <> C1 ->
 B <> B1 ->
 C <> S ->
 B <> S ->
 C1 <> S ->
 B1 <> S ->
 A1 <> B1 ->
 A1 <> C1 ->
 B <> C ->
 B1 <> C1 ->
 triangle A A1 B ->
 triangle A A1 C ->
 alignes A A1 S ->
 alignes B B1 S ->
 alignes C C1 S ->
 paralleles (droite A B) (droite A1 B1) ->
 paralleles (droite A C) (droite A1 C1) ->
 paralleles (droite B C) (droite B1 C1).
intros.
deroule_triangle A A1 B.
deroule_triangle A A1 C.
elim Thales_PP with (3 := H15); intros; auto.
elim Thales_PP with (3 := H14); intros; auto.
apply reciproque_Thales_PP with x; auto.
elim (classic (1 + x = 0)); intros.
cut (x = -1); [ intros | auto ].
rewrite H27 in H24.
absurd (add_PP (cons 1 A) (cons (-1) A1) = add_PP (cons 1 C) (cons (-1) C1));
 auto.
apply parallelogramme_non_concours with S; auto.
replace x with (-1 + (1 + x)); auto.
rewrite H26.
ring.
ring.
elim (classic (1 + x0 = 0)); intros.
cut (x0 = -1); [ intros | auto ].
rewrite H28 in H25.
absurd (add_PP (cons 1 A) (cons (-1) A1) = add_PP (cons 1 B) (cons (-1) B1));
 auto.
apply parallelogramme_non_concours with S; auto.
replace x0 with (-1 + (1 + x0)); auto.
rewrite H27.
ring.
ring.
rewrite add_PP_barycentre; auto.
rewrite add_PP_barycentre; auto.
cut (barycentre (cons 1 A) (cons x A1) = barycentre (cons 1 C) (cons x C1));
 intros.
cut (barycentre (cons 1 A) (cons x0 A1) = barycentre (cons 1 B) (cons x0 B1));
 intros.
cut
 (S = barycentre (cons 1 A) (cons x A1) /\
  S = barycentre (cons 1 A) (cons x0 A1)); intros.
cut (x = x0); [ intros | auto ].
elim H30; intros; try clear H30.
rewrite <- H28; auto.
rewrite H31.
rewrite <- H29; auto.
apply unicite_coef_bar with (A := A) (B := A1) (x := x) (x0 := x0); auto.
elim H30; intros; try clear H30.
rewrite <- H31; auto.
split; [ try assumption | idtac ].
apply concours_unique with (A := A) (B := C) (A1 := A1) (B1 := C1);
 auto with geo.
rewrite H28.
rewrite permute_barycentre; auto.
apply barycentre_alignes; auto.
replace (x + 1) with (1 + x); auto.
ring.
apply concours_unique with (A := A) (B := B) (A1 := A1) (B1 := B1);
 auto with geo.
rewrite H29.
rewrite permute_barycentre; auto.
apply barycentre_alignes; auto.
replace (x0 + 1) with (1 + x0); auto.
ring.
apply conversion_PP with (a := 1 + x0) (b := 1 + x0); auto with *.
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
apply conversion_PP with (a := 1 + x) (b := 1 + x); auto with *.
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
Qed.
 
Lemma Thales_concours :
 forall (k : R) (A B C I J : PO),
 triangle A B C ->
 k <> 0 :>R ->
 vec A I = mult_PP k (vec A B) :>PP ->
 paralleles (droite B C) (droite I J) ->
 alignes A C J -> vec A J = mult_PP k (vec A C) :>PP.
intros k A B C I J H H0 H2 H3 H4; try assumption.
elim (classic (k = 1)); intros.
cut (B = I); intros.
cut (J = C); intros.
rewrite H6; rewrite H1; Ringvec.
generalize (alignes_paralleles_confondus (A:=A) (B:=B)); intros H16;
 apply H16; auto.
pattern B at 2 in |- *; rewrite H5; auto.
apply vecteur_nul_conf.
replace (vec B I) with (add_PP (mult_PP (-1) (vec A B)) (vec A I));
 [ idtac | Ringvec ].
rewrite H2; rewrite H1; Ringvec.
generalize H2; unfold vec in |- *; intros H98.
deroule_triangle A B C.
cut (1 + - k <> 0).
intros H102.
cut (- k <> 0).
intros H103.
cut (1 + - / k <> 0).
intros H104.
cut (B <> I).
intros H99.
cut (I <> J); intros.
cut (alignes B I A).
intros H100.
cut (~ alignes B I C).
intros H101.
elim Thales_PP with (A := B) (B := I) (C := C) (D := J);
 [ intros x H10; try clear Thales_PP; try exact H10 | auto | auto | auto ].
elim (classic (x = -1)); intros.
cut (C <> J); intros.
rewrite H11 in H10.
absurd (add_PP (cons 1 B) (cons (-1) I) = add_PP (cons 1 C) (cons (-1) J));
 auto.
apply parallelogramme_non_concours with A; auto with geo.
red in |- *; intros; apply H99.
apply conversion_PP with (a := 1) (b := 1); try ring.
RingPP1 H10.
rewrite H11; rewrite H12; RingPP.
discrR.
cut (1 + x <> 0); intros.
cut (C <> J); intros.
cut (barycentre (cons 1 B) (cons x I) = barycentre (cons 1 C) (cons x J));
 intros.
cut (cons 1 J = add_PP (cons (1 + - k) A) (cons k C)); intros.
rewrite H15; RingPP.
cut (A = barycentre (cons 1 B) (cons x I)); intros.
cut (A = barycentre (cons (- k) B) (cons 1 I)); intros.
cut (x = - / k); intros.
rewrite <- H15 in H14.
rewrite H17 in H14.
rewrite H17 in H15.
cut (A = barycentre (cons (- k) C) (cons 1 J)); intros.
rewrite H18.
replace (1 + - k) with (- k + 1); [ idtac | ring ].
rewrite <- add_PP_barycentre; auto.
RingPP.
replace (- k + 1) with (1 + - k); [ auto | ring ].
rewrite H14.
rewrite <- homogene_barycentre with (k := - k); auto.
replace (- k * 1) with (- k) by ring.
replace (- k * - / k) with 1 by (field;trivial).
reflexivity.



cut (A = barycentre (cons 1 B) (cons (- / k) I)); intros.
apply unicite_coef_bar with (A := B) (B := I) (x := x) (x0 := - / k); auto.
rewrite <- H15; auto.
rewrite H16.
symmetry  in |- *.
rewrite <- homogene_barycentre with (k := - k); auto.
replace (- k * 1) with (- k) by ring.
replace (- k * - / k) with 1 by (field;trivial).
reflexivity.
cut (cons (1 + - k) A = add_PP (cons 1 I) (cons (- k) B)); intros.
rewrite permute_barycentre; auto.
apply conversion_PP with (a := 1 + - k) (b := 1 + - k); auto.
rewrite <- add_PP_barycentre; auto.
replace (- k + 1) with (1 + - k); [ auto | ring ].
RingPP2 H98; RingPP.
apply concours_unique with (A := B) (B := C) (A1 := I) (B1 := J); auto.
apply permute_alignes; auto with geo.
apply barycentre_alignes; auto.
rewrite H14.
apply permute_alignes; auto.
apply barycentre_alignes; auto.
apply conversion_PP with (a := 1 + x) (b := 1 + x); auto.
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
red in |- *; intros; apply H101.
replace C with (barycentre (cons 1 B) (cons x I)).
apply barycentre_alignes; auto.
apply conversion_PP with (a := 1 + x) (b := 1 + x); try ring; auto.
rewrite <- add_PP_barycentre; auto.
rewrite H10; rewrite H13; Ringvec.
red in |- *; intros; apply H11.
replace (-1) with (-1 + 0) by ring.
rewrite <- H12; ring.
cut (~ alignes B A C); intros; auto with geo.
red in |- *; intros; apply H10.
halignes H11 ipattern:y.
apply colineaire_alignes with ((1 + - k) * y).
rewrite H12; unfold vec in |- *.
RingPP2 H98.
replace
 (add_PP (mult_PP k (add_PP (cons (-1) A) (cons 1 B)))
    (mult_PP (-1) (cons (-1) A))) with (add_PP (cons (1 + - k) A) (cons k B));
 [ idtac | RingPP ].
replace (add_PP (cons (-1) B) (add_PP (cons (1 + - k) A) (cons k B))) with
 (add_PP (cons (1 + - k) A) (cons (-1 * (1 + - k)) B)); 
 [ idtac | RingPP ].
replace ((1 + - k) * y) with (y * (1 + - k)); [ idtac | ring ].
RingPP.
apply colineaire_alignes with (/ (1 + - k)).
replace (vec B I) with (add_PP (vec B A) (vec A I)); [ idtac | Ringvec ].
rewrite H2.
Fieldvec (1 + - k).
cut (~ alignes A C B); intros; auto with geo.
red in |- *; intros; apply H9.
halignes H4 ipattern:x.
apply colineaire_alignes with (/ k * x).
apply mult_PP_regulier with k; auto.
rewrite <- H2; rewrite H10; rewrite H11.
Fieldvec k.
red in |- *; intros; apply H102.
elim produit_vecteur_nul with (a := 1 + - k) (A := A) (B := B);
 [ intros H10; try clear produit_vecteur_nul; try exact H10
 | intros H10; try clear produit_vecteur_nul
 | try clear produit_vecteur_nul ].
absurd (A = B); auto.
replace (mult_PP (1 + - k) (vec A B)) with
 (add_PP (vec A B) (mult_PP (-1) (mult_PP k (vec A B)))); 
 [ idtac | Ringvec ].
rewrite <- H2; rewrite H9; Ringvec.
replace (1 + - / k) with (- / k * (1 + - k)); try ring; auto.
apply integre_not; auto with real.
field.
auto with real.
auto with real.
red in |- *; intros; apply H1.
replace 1 with (1 + - k + k); [ idtac | ring ].
rewrite H9; ring.
Qed.
 
Lemma reciproque_droite_milieu :
 forall A B C I J : PO,
 triangle A B C ->
 I = milieu A B :>PO ->
 paralleles (droite B C) (droite I J) -> alignes A C J -> J = milieu A C :>PO.
intros.
apply vecteur_milieu.
apply (Thales_concours (k:=/ 2) (A:=A) (B:=B) (C:=C) (I:=I) (J:=J)); auto.
cut (2 <> 0); intros.
auto with real.
discrR.
apply milieu_vecteur2; auto.
Qed.
