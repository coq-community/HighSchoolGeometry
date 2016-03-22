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
 
Definition translation (I J A : PO) :=
  barycentre (cons (-1) I) (cons 2 (barycentre (cons 1 J) (cons 1 A))).
 
Lemma translation_vecteur :
 forall I J A A' : PO, A' = translation I J A -> vec I J = vec A A'.
unfold vec, translation in |- *; intros.
rewrite H.
pattern 1 at 4 in |- *.
replace 1 with (-1 + 2); try ring.
repeat rewrite <- add_PP_barycentre; try discrR; auto.
RingPP.
Qed.
 
Lemma translation_identite :
 forall I A A' : PO, A' = translation I I A :>PO -> A = A'.
intros.
apply vecteur_nul_conf; auto.
rewrite <- (translation_vecteur (I:=I) (J:=I) (A:=A) (A':=A')); auto.
Ringvec.
Qed.
 
Lemma rec_translation_vecteur :
 forall I J A A' : PO, vec I J = vec A A' :>PP -> A' = translation I J A :>PO.
unfold vec, translation in |- *; intros.
elim
 cons_inj
  with
    (a := 1)
    (b := -1 + 2)
    (A := A')
    (B := barycentre (cons (-1) I)
            (cons 2 (barycentre (cons 1 J) (cons 1 A)))); 
 intros; auto with *.
repeat rewrite <- add_PP_barycentre; try discrR.
RingPP1 H.
RingPP.
Qed.
 
Lemma translation_trivial : forall I J : PO, J = translation I J I.
intros.
apply rec_translation_vecteur; auto.
Qed.
Hint Resolve translation_trivial: geo.
 
Lemma translation_bipoint :
 forall I J A A' B B' : PO,
 A' = translation I J A :>PO ->
 B' = translation I J B :>PO -> vec A B = vec A' B'.
intros I J A A' B B' H H0; try assumption.
apply egalite_vecteur.
rewrite <- (translation_vecteur (I:=I) (J:=J) (A:=A) (A':=A')); auto.
rewrite <- (translation_vecteur (I:=I) (J:=J) (A:=B) (A':=B')); auto.
Qed.
 
Lemma translation_trans :
 forall I J A A' B B' : PO,
 A' = translation I J A :>PO ->
 B' = translation I J B :>PO -> B' = translation A A' B :>PO.
intros I J A A' B B' H H0; try assumption.
apply rec_translation_vecteur.
rewrite <- (translation_vecteur (I:=I) (J:=J) (A:=A) (A':=A')); auto.
rewrite <- (translation_vecteur (I:=I) (J:=J) (A:=B) (A':=B')); auto.
Qed.
 
Lemma image_translation_distincts :
 forall I J A A' B B' : PO,
 A <> B -> A' = translation I J A :>PO -> B' = translation I J B -> A' <> B'.
intros.
apply distinct_egalite_vecteur with (A := A) (B := B); auto.
symmetry  in |- *; apply translation_bipoint with (I := I) (J := J); auto.
Qed.
 
Lemma translation_droite :
 forall I J A A' B B' : PO,
 A <> B ->
 A' = translation I J A :>PO ->
 B' = translation I J B :>PO -> paralleles (droite A' B') (droite A B).
intros.
apply colineaires_paralleles with 1; auto.
apply image_translation_distincts with (2 := H0) (3 := H1); auto.
replace (mult_PP 1 (vec A B)) with (vec A B).
symmetry  in |- *; apply translation_bipoint with (I := I) (J := J); auto.
Ringvec.
Qed.
 
Lemma translation_milieu :
 forall I J A A' B B' M N : PO,
 A' = translation I J A :>PO ->
 B' = translation I J B ->
 M = milieu A B -> N = milieu A' B' -> N = translation I J M.
intros I J A A' B B' M N H H0 H1 H2; try assumption.
apply rec_translation_vecteur; auto.
replace (vec M N) with (add_PP (cons (-1) M) (cons 1 N)); auto.
apply mult_PP_regulier with 2; try discrR.
repeat rewrite <- distrib_mult_cons.
replace (2 * 1) with 2; try ring; auto.
rewrite H2.
rewrite <- add_PP_milieu.
replace (2 * -1) with (-1 * 2); try ring; auto.
repeat rewrite <- def_mult_PP.
rewrite H1.
rewrite <- add_PP_milieu.
repeat rewrite <- distrib_mult_cons.
replace (-1 * 1) with (-1); try ring; auto.
rewrite <- calcul; auto.
replace (add_PP (cons (-1) B) (cons 1 B')) with (vec B B'); auto.
rewrite <- (translation_vecteur (I:=A) (J:=A') (A:=B) (A':=B')); auto.
rewrite (translation_vecteur (I:=I) (J:=J) (A:=A) (A':=A')); auto.
Ringvec.
apply translation_trans with (1 := H); auto.
Qed.
 
Lemma translation_alignement :
 forall I J A A' B B' C C' : PO,
 A' = translation I J A :>PO ->
 B' = translation I J B :>PO ->
 C' = translation I J C -> alignes A B C -> alignes A' B' C'.
intros I J A A' B B' C C' H H0 H1 H2; try assumption.
discrimine A B.
assert (A' = B'); auto with geo.
rewrite H0; rewrite <- H3; auto.
halignes H2 ipattern:k.
apply colineaire_alignes with k.
rewrite <-
 (translation_bipoint (I:=I) (J:=J) (A:=A) (A':=A') (B:=B) (B':=B'))
 ; auto.
rewrite <- H4; auto.
rewrite <-
 (translation_bipoint (I:=I) (J:=J) (A:=A) (A':=A') (B:=C) (B':=C'))
 ; auto.
Qed.
 
Lemma translation_inverse :
 forall I J A A' : PO,
 A' = translation I J A :>PO -> A = translation J I A' :>PO.
intros.
apply rec_translation_vecteur; auto.
VReplace (vec J I) (mult_PP (-1) (vec I J)).
rewrite (translation_vecteur (I:=I) (J:=J) (A:=A) (A':=A')); auto.
Ringvec.
Qed.
Hint Resolve translation_inverse: geo.
 
Lemma translation_intersection :
 forall I J A A' B B' C C' D D' K K' : PO,
 A <> B ->
 C <> D ->
 ~ alignes A B C \/ ~ alignes A B D ->
 K = pt_intersection (droite A B) (droite C D) ->
 A' = translation I J A :>PO ->
 B' = translation I J B ->
 C' = translation I J C :>PO ->
 D' = translation I J D :>PO ->
 K' = translation I J K :>PO ->
 K' = pt_intersection (droite A' B') (droite C' D').
intros.
elim def_pt_intersection2 with (A := A) (B := B) (C := C) (D := D) (I := K);
 [ try clear def_pt_intersection2; intros | auto | auto | auto | auto ].
apply def_pt_intersection; auto.
apply image_translation_distincts with (2 := H3) (3 := H4); auto.
apply image_translation_distincts with (2 := H5) (3 := H6); auto.
elim H1;
 [ intros H10; try clear H1 | intros H10; try clear H1; try exact H10 ].
left.
red in |- *; intros; apply H10.
apply
 (translation_alignement (I:=J) (J:=I) (A:=A') (A':=A) (B:=B') (B':=B)
    (C:=C') (C':=C)); auto with geo.
right; red in |- *; intros H1; apply H10.
apply
 (translation_alignement (I:=J) (J:=I) (A:=A') (A':=A) (B:=B') (B':=B)
    (C:=D') (C':=D)); auto with geo.
apply
 (translation_alignement (I:=I) (J:=J) (A:=A) (A':=A') (B:=B) (B':=B') (C:=K)
    (C':=K')); auto with geo.
apply
 (translation_alignement (I:=I) (J:=J) (A:=C) (A':=C') (B:=D) (B':=D') (C:=K)
    (C':=K')); auto with geo.
Qed.
 
Lemma translation_paralleles :
 forall I J A A' B B' C C' D D' : PO,
 A <> B ->
 C <> D ->
 paralleles (droite A B) (droite C D) ->
 A' = translation I J A :>PO ->
 B' = translation I J B ->
 C' = translation I J C :>PO ->
 D' = translation I J D :>PO -> paralleles (droite A' B') (droite C' D').
intros.
elim paralleles_vecteur with (A := A) (B := B) (C := C) (D := D);
 [ intros k H6; try clear paralleles_vecteur; try exact H6
 | auto
 | auto
 | auto ].
apply colineaires_paralleles with k.
apply distinct_egalite_vecteur with (A := A) (B := B); auto.
symmetry  in |- *; apply translation_bipoint with (I := I) (J := J); auto.
apply distinct_egalite_vecteur with (A := C) (B := D); auto.
symmetry  in |- *; apply translation_bipoint with (I := I) (J := J); auto.
rewrite <-
 (translation_bipoint (I:=I) (J:=J) (A:=C) (A':=C') (B:=D) (B':=D'))
 ; auto.
rewrite <- H6; auto.
symmetry  in |- *; apply translation_bipoint with (I := I) (J := J); auto.
Qed.
 
Definition homothetie (k : R) (I A : PO) :=
  barycentre (cons k A) (cons (1 + - k) I).
 
Lemma homothetie_identite : forall I A : PO, A = homothetie 1 I A.
unfold homothetie, vec in |- *; intros.
replace (1 + -1) with 0; try ring; auto.
rewrite barycentre_zero; auto with *.
Qed.
 
Lemma vecteur_homothetie :
 forall (k : R) (I A A' : PO),
 vec I A' = mult_PP k (vec I A) :>PP -> A' = homothetie k I A :>PO.
unfold vec, homothetie in |- *; intros.
elim
 cons_inj
  with
    (a := 1)
    (b := k + (1 + - k))
    (A := A')
    (B := barycentre (cons k A) (cons (1 + - k) I)); 
 intros; auto with *.
repeat rewrite <- add_PP_barycentre; try discrR.
RingPP2 H.
RingPP.
replace (k + (1 + - k)) with 1; try ring; try discrR.
Qed.
 
Lemma homothetie_centre : forall (I : PO) (k : R), I = homothetie k I I.
intros.
apply vecteur_homothetie.
Ringvec.
Qed.
Hint Resolve homothetie_centre: geo.
 
Lemma homothetie_vecteur :
 forall (k : R) (I A A' : PO),
 A' = homothetie k I A -> vec I A' = mult_PP k (vec I A).
unfold homothetie, vec in |- *; intros.
rewrite H.
pattern 1 at 2 in |- *.
replace 1 with (k + (1 + - k)); try ring.
repeat rewrite <- add_PP_barycentre; try discrR.
RingPP.
replace (k + (1 + - k)) with 1; try ring.
try discrR.
Qed.
 
Definition symetrie (I A : PO) := homothetie (-1) I A.
 
Lemma milieu_symetrie :
 forall A B I : PO, I = milieu A B :>PO -> B = symetrie I A :>PO.
unfold symetrie in |- *; intros.
apply vecteur_homothetie.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=I)); auto.
Ringvec.
Qed.
 
Lemma symetrie_milieu :
 forall A B I : PO, B = symetrie I A :>PO -> I = milieu A B :>PO.
unfold symetrie in |- *; intros.
cut (vec I B = mult_PP (-1) (vec I A)); intros.
2: apply homothetie_vecteur; auto.
apply vecteur_milieu.
replace (vec A B) with (add_PP (vec A I) (vec I B)); [ idtac | Ringvec ].
rewrite H0.
cut (2 <> 0); intros; auto with real.
Fieldvec 2.
Qed.
Hint Resolve milieu_symetrie symetrie_milieu: geo.
 
Lemma symetrie_involution :
 forall A B I : PO, B = symetrie I A :>PO -> A = symetrie I B :>PO.
intros.
apply milieu_symetrie.
apply milieu_permute.
apply symetrie_milieu; auto.
Qed.
 
Lemma existence_homothetique :
 forall (k : R) (I A : PO), exists A' : PO, A' = homothetie k I A.
intros.
elim
 existence_representant_mult_vecteur with (A := I) (B := I) (C := A) (k := k);
 intros A' H1; try clear existence_representant_mult_vecteur.
exists A'.
apply vecteur_homothetie; auto.
Qed.
 
Lemma existence_symetrique : forall A B : PO, exists C : PO, C = symetrie A B.
unfold symetrie in |- *; intros.
apply (existence_homothetique (-1) A B).
Qed.
 
Ltac symetrique O A B :=
  elim (existence_symetrique O A); intros B; intros; assert (O = milieu A B);
   auto with geo.
 
Lemma existence_symetrique_milieu:
 forall (A I : PO),  (exists B : PO , I = milieu A B ).
intros.
elim (existence_symetrique I A);
 [intros B H; (try clear existence_symetrique); (try exact H)].
exists B.
apply symetrie_milieu; auto.
Qed.
 
Lemma unicite_symetrique:
 forall (A B P : PO), milieu A P = milieu B P ->  A = B.
intros.
elim (existence_milieu B P); [intros I H1; (try clear existence_milieu)].
assert (B = symetrie I P).
apply milieu_symetrie; auto with geo.
rewrite H0.
apply milieu_symetrie.
rewrite H1.
auto with geo.
Qed.

Lemma homothetie_bipoint :
 forall (k : R) (I A B A' B' : PO),
 A' = homothetie k I A ->
 B' = homothetie k I B -> vec A' B' = mult_PP k (vec A B).
unfold homothetie, vec in |- *; intros.
rewrite H.
rewrite H0.
replace (cons (-1) (barycentre (cons k A) (cons (1 + - k) I))) with
 (mult_PP (-1) (cons 1 (barycentre (cons k A) (cons (1 + - k) I)))); 
 try ring; auto.
pattern 1 at 2 in |- *.
replace 1 with (k + (1 + - k)); try ring.
pattern 1 at 4 in |- *.
replace 1 with (k + (1 + - k)); try ring.
repeat rewrite <- add_PP_barycentre; try discrR.
RingPP.
replace (k + (1 + - k)) with 1; try ring.
try discrR.
replace (k + (1 + - k)) with 1; try ring.
try discrR.
RingPP.
Qed.
 
Lemma homothetie_milieu :
 forall (k : R) (I A A' B B' M N : PO),
 k <> 0 ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B :>PO ->
 M = milieu A B :>PO -> N = milieu A' B' :>PO -> homothetie k I M = N.
unfold homothetie, milieu in |- *; intros.
rewrite H2; rewrite H3; rewrite H1; rewrite H0.
elim
 cons_inj
  with
    (a := 2)
    (b := 2)
    (A := barycentre (cons k (barycentre (cons 1 A) (cons 1 B)))
            (cons (1 + - k) I))
    (B := barycentre (cons 1 (barycentre (cons k A) (cons (1 + - k) I)))
            (cons 1 (barycentre (cons k B) (cons (1 + - k) I))));
 (intros; auto); try discrR.
repeat rewrite <- add_PP_barycentre; try discrR.
replace 2 with (2 * (k + (1 + - k))); try ring; auto.
rewrite <-
 (homogene_barycentre (a:=k) (b:=1 + - k) (k:=2)
    (barycentre (cons 1 A) (cons 1 B)) I); try discrR.
replace (2 * (k + (1 + - k))) with (2 * k + 2 * (1 + - k)); try ring;
 try discrR.
repeat rewrite <- add_PP_barycentre; try discrR.
rewrite <- (homogene_barycentre (a:=1) (b:=1) (k:=k) A B); auto; try discrR.
replace (2 * k) with (k * 1 + k * 1); try ring; auto.
repeat rewrite <- add_PP_barycentre; auto; try discrR.
pattern 1 at 6 in |- *.
replace 1 with (k + (1 + - k)); try ring; auto.
repeat rewrite <- add_PP_barycentre; try discrR.
pattern 1 at 7 in |- *.
replace 1 with (k + (1 + - k)); try ring; auto.
repeat rewrite <- add_PP_barycentre; try discrR.
RingPP.
replace (k + (1 + - k)) with 1; try ring; try discrR.
replace (k + (1 + - k)) with 1; try ring; try discrR.
replace (k * 1 + k * 1) with (k * 2); try ring; auto.
apply Rmult_integral_contrapositive; (split; auto; try discrR).
replace (2 * k + 2 * (1 + - k)) with (2 * 1); try ring; try discrR.
replace (k + (1 + - k)) with 1; try ring; try discrR.
Qed.
 
Lemma image_homothetie_distincts :
 forall (k : R) (I A A' B B' : PO),
 k <> 0 :>R ->
 A <> B -> A' = homothetie k I A :>PO -> B' = homothetie k I B -> A' <> B'.
intros.
cut (vec A' B' <> zero); intros.
red in |- *; intros; apply H3; auto.
rewrite H4; Ringvec.
rewrite (homothetie_bipoint (k:=k) (I:=I) (A:=A) (B:=B) (A':=A') (B':=B'));
 auto.
red in |- *; intros.
elim produit_vecteur_nul with (a := k) (A := A) (B := B);
 [ intros; try trivial | intros; try trivial | try trivial ].
absurd (k = 0); auto.
absurd (A = B); auto.
Qed.
 
Lemma homothetie_droite :
 forall (k : R) (I A A' B B' : PO),
 k <> 0 :>R ->
 A <> B ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B :>PO -> paralleles (droite A' B') (droite A B).
intros.
apply colineaires_paralleles with k; auto.
apply image_homothetie_distincts with (3 := H1) (4 := H2); auto.
apply homothetie_bipoint with (I := I); auto.
Qed.
 
Lemma homothetie_inverse :
 forall (k : R) (I A A' : PO),
 k <> 0 :>R -> A' = homothetie k I A :>PO -> A = homothetie (/ k) I A' :>PO.
intros.
apply vecteur_homothetie.
rewrite (homothetie_vecteur (k:=k) (I:=I) (A:=A) (A':=A')); auto.
Fieldvec k.
Qed.
Hint Resolve homothetie_inverse: geo.
 
Lemma homothetie_alignement :
 forall (k : R) (I A B A' B' C C' : PO),
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B :>PO ->
 C' = homothetie k I C -> alignes A B C -> alignes A' B' C'.
intros k I A B A' B' C C' H H0 H1 H2; try assumption.
discrimine A B.
assert (A' = B'); auto with geo.
rewrite H0; rewrite <- H3; auto.
halignes H2 ipattern:k0.
apply colineaire_alignes with k0.
rewrite (homothetie_bipoint (k:=k) (I:=I) (A:=A) (B:=B) (A':=A') (B':=B'));
 auto.
rewrite (homothetie_bipoint (k:=k) (I:=I) (A:=A) (B:=C) (A':=A') (B':=C'));
 auto.
rewrite H4.
Ringvec.
Qed.
 
Lemma homothetie_paralleles :
 forall (k : R) (I A A' B B' C C' D D' : PO),
 k <> 0 :>R ->
 A <> B ->
 C <> D ->
 paralleles (droite A B) (droite C D) ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B ->
 C' = homothetie k I C :>PO ->
 D' = homothetie k I D :>PO -> paralleles (droite A' B') (droite C' D').
intros.
elim paralleles_vecteur with (A := A) (B := B) (C := C) (D := D);
 [ intros x H7; try clear paralleles_vecteur | auto | auto | auto ].
apply colineaires_paralleles with x.
apply
 (image_homothetie_distincts (k:=k) (I:=I) (A:=A) (A':=A') (B:=B) (B':=B'));
 auto.
apply
 (image_homothetie_distincts (k:=k) (I:=I) (A:=C) (A':=C') (B:=D) (B':=D'));
 auto.
rewrite (homothetie_bipoint (k:=k) (I:=I) (A:=A) (B:=B) (A':=A') (B':=B'));
 auto.
rewrite (homothetie_bipoint (k:=k) (I:=I) (A:=C) (B:=D) (A':=C') (B':=D'));
 auto.
rewrite H7; Ringvec.
Qed.
 
Lemma homothetie_intersection :
 forall (k : R) (I A A' B B' C C' D D' K K' : PO),
 k <> 0 :>R ->
 A <> B ->
 C <> D ->
 ~ alignes A B C \/ ~ alignes A B D ->
 K = pt_intersection (droite A B) (droite C D) :>PO ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B ->
 C' = homothetie k I C :>PO ->
 D' = homothetie k I D :>PO ->
 K' = homothetie k I K :>PO ->
 K' = pt_intersection (droite A' B') (droite C' D') :>PO.
intros.
elim def_pt_intersection2 with (A := A) (B := B) (C := C) (D := D) (I := K);
 [ try clear def_pt_intersection2; intros | auto | auto | auto | auto ].
apply def_pt_intersection; auto.
apply image_homothetie_distincts with (3 := H4) (4 := H5); auto.
apply image_homothetie_distincts with (3 := H6) (4 := H7); auto.
elim H2;
 [ intros H11; try clear H2 | intros H11; try clear H2; try exact H11 ].
left.
red in |- *; intros; apply H11.
apply
 (homothetie_alignement (k:=/ k) (I:=I) (A:=A') (B:=B') (A':=A) (B':=B)
    (C:=C') (C':=C)); auto with geo.
right; red in |- *; intros H2; apply H11.
apply
 (homothetie_alignement (k:=/ k) (I:=I) (A:=A') (B:=B') (A':=A) (B':=B)
    (C:=D') (C':=D)); auto with geo.
apply
 (homothetie_alignement (k:=k) (I:=I) (A:=A) (B:=B) (A':=A') (B':=B') (C:=K)
    (C':=K')); auto with geo.
apply
 (homothetie_alignement (k:=k) (I:=I) (A:=C) (B:=D) (A':=C') (B':=D') (C:=K)
    (C':=K')); auto with geo.
Qed.
 
Lemma paralleles_dilatations :
 forall A A' B B' : PO,
 A <> B ->
 A' <> B' ->
 paralleles (droite A' B') (droite A B) ->
 (exists I : PO,
    (exists J : PO, A' = translation I J A /\ B' = translation I J B)) \/
 (exists k : R,
    (exists I : PO, A' = homothetie k I A /\ B' = homothetie k I B)).
intros.
elim paralleles_vecteur with (A := A') (B := B') (C := A) (D := B);
 [ intros k H2; try clear paralleles_vecteur; try exact H2
 | trivial
 | trivial
 | trivial ].
elim (classic (k = 0)); intros; auto.
absurd (A' = B'); intros; auto.
apply vecteur_nul_conf; auto.
rewrite H2; rewrite H3; Ringvec.
elim (classic (k = 1)); intros; auto.
rewrite H4 in H2.
left; try assumption.
exists A; exists A'.
split; apply rec_translation_vecteur; auto.
apply egalite_vecteur; rewrite H2; Ringvec.
right; try assumption.
exists k; exists (barycentre (cons (- k) A) (cons 1 A')).
cut (A' = homothetie k (barycentre (cons (- k) A) (cons 1 A')) A).
intros H20.
split; [ try assumption | idtac ].
apply vecteur_homothetie.
replace (vec (barycentre (cons (- k) A) (cons 1 A')) B') with
 (add_PP (vec (barycentre (cons (- k) A) (cons 1 A')) A') (vec A' B')).
cut
 (vec (barycentre (cons (- k) A) (cons 1 A')) A' =
  mult_PP k (vec (barycentre (cons (- k) A) (cons 1 A')) A)); 
 intros.
rewrite H5; rewrite H2; Ringvec.
apply homothetie_vecteur; auto.
Ringvec.
unfold homothetie in |- *.
replace (1 + - k) with (- k + 1); try ring; auto.
apply conversion_PP with (a := 1) (b := 1); auto with real.
pattern 1 at 2 in |- *.
replace 1 with (k + (- k + 1)); try ring; auto.
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
RingPP.
red in |- *; intros; apply H4.
replace 1 with (k + (- k + 1)).
rewrite H5; try ring.
ring.
replace (k + (- k + 1)) with 1; try ring; auto with real.
Qed.