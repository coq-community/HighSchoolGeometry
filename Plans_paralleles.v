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


Require Export Droite_plan_espace.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter para_plan_plan : PL -> PL -> Prop.
 
Axiom
  def_para_plan_plan :
    forall A B C D E F : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    para_plan_dr (plan A B C) (droite D E) ->
    para_plan_dr (plan A B C) (droite D F) ->
    para_plan_plan (plan A B C) (plan D E F).
 
Axiom
  def_para_plan_plan2 :
    forall A B C D E F : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    para_plan_plan (plan A B C) (plan D E F) ->
    para_plan_dr (plan A B C) (droite D E) /\
    para_plan_dr (plan A B C) (droite D F).
 
Lemma couple_vecteurs_coplanaires :
 forall (A B C D E F : PO) (a b c d : R),
 ~ alignes A B C ->
 ~ alignes D E F ->
 vec D E = add_PP (mult_PP a (vec A B)) (mult_PP b (vec A C)) :>PP ->
 vec D F = add_PP (mult_PP c (vec A B)) (mult_PP d (vec A C)) :>PP ->
 para_plan_plan (plan A B C) (plan D E F).
intros.
deroule_triangle D E F.
apply def_para_plan_plan; auto.
apply vecteurs_para_plan_dr with (k := a) (k' := b); auto.
apply vecteurs_para_plan_dr with (k := c) (k' := d); auto.
Qed.
 
Lemma plans_paralleles_vecteurs :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 para_plan_plan (plan A B C) (plan D E F) ->
 (exists a : R,
    (exists b : R,
       vec D E = add_PP (mult_PP a (vec A B)) (mult_PP b (vec A C)) :>PP)) /\
 (exists c : R,
    (exists d : R,
       vec D F = add_PP (mult_PP c (vec A B)) (mult_PP d (vec A C)) :>PP)).
intros.
elim def_para_plan_plan2 with (3 := H1);
 [ try clear def_para_plan_plan2; auto | auto | auto ].
intros.
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros k H5; elim H5; intros k' H6; try clear H5 para_plan_dr_vecteur;
    try exact H6
 | auto with geo
 | auto
 | auto ].
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros k0 H7; elim H7; intros k'0 H8; try clear H7 para_plan_dr_vecteur;
    try exact H8
 | auto with geo
 | auto
 | auto ].
split; [ exists k | idtac ].
exists k'; auto.
exists k0; exists k'0; auto.
deroule_triangle D E F; auto.
Qed.
 
Lemma paralleles_droites_plan_trans :
 forall A B C D E F G : PO,
 ~ alignes A B C ->
 D <> E :>PO ->
 F <> G :>PO ->
 para_plan_dr (plan A B C) (droite D E) ->
 paralleles (droite D E) (droite F G) ->
 para_plan_dr (plan A B C) (droite F G).
intros.
elim def_para_plan_dr2 with (A := A) (B := B) (C := C) (F := D) (G := E);
 [ intros D0 H5; elim H5; intros E0 H6; elim H6; intros H7 H8; elim H8;
    intros H9 H10; try clear H8 H6 H5 def_para_plan_dr2; 
    try exact H10
 | auto
 | auto
 | auto ].
apply def_para_plan_dr with (D := D0) (E := E0); auto.
elim H6; intros H4 H11; elim H4; intros H12 H13; try clear H4 H6;
 try exact H12.
elim H7; intros H4 H11; try clear H7; try exact H11.
apply paralleles_trans with (4 := H10); auto.
Qed.
 
Lemma para_plan_refl :
 forall A B C : PO,
 ~ alignes A B C -> para_plan_plan (plan A B C) (plan A B C).
intros.
deroule_triangle A B C.
generalize
 (couple_vecteurs_coplanaires (A:=A) (B:=B) (C:=C) (D:=A) (E:=B) (F:=C)
    (a:=1) (b:=0) (c:=0) (d:=1)); intros H11; apply H11; 
 auto.
unfold vec in |- *; RingPP.
unfold vec in |- *; RingPP.
Qed.
 
Lemma para_plan_sym :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 para_plan_plan (plan A B C) (plan D E F) ->
 para_plan_plan (plan D E F) (plan A B C).
intros A B C D E F H H0 H1; try assumption.
elim
 def_para_plan_plan2
  with (A := A) (B := B) (C := C) (D := D) (E := E) (F := F);
 [ intros H2 H3; try clear def_para_plan_plan2; try exact H3
 | auto
 | auto
 | auto ].
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros k H8; elim H8; intros k' H9; try clear H8 para_plan_dr_vecteur;
    auto
 | auto
 | auto
 | auto ].
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros k0 H10; elim H10; intros k'0 H11;
    try clear H10 para_plan_dr_vecteur; try exact H11
 | auto
 | auto
 | auto ].
cut
 (ex
    (fun a : R =>
     ex
       (fun b : R =>
        vec A B = add_PP (mult_PP a (vec D E)) (mult_PP b (vec D F)))) /\
  ex
    (fun c : R =>
     ex
       (fun d : R =>
        vec A C = add_PP (mult_PP c (vec D E)) (mult_PP d (vec D F))))).
intros H12.
elim H12; intros H13 H14; elim H13; intros a H15; elim H15; intros b H16;
 try clear H15 H13 H12; try exact H16.
elim H14; intros c H12; elim H12; intros d H13; try clear H12 H14;
 try exact H13.
apply couple_vecteurs_coplanaires with (a := a) (b := b) (c := c) (d := d);
 auto.
cut
 (mult_PP k (vec D F) =
  add_PP (mult_PP (k * k0) (vec A B)) (mult_PP (k * k'0) (vec A C))); 
 intros.
cut
 (mult_PP k' (vec D F) =
  add_PP (mult_PP (k' * k0) (vec A B)) (mult_PP (k' * k'0) (vec A C)));
 intros.
cut
 (mult_PP k0 (vec D E) =
  add_PP (mult_PP (k0 * k) (vec A B)) (mult_PP (k0 * k') (vec A C))); 
 intros.
cut
 (mult_PP k'0 (vec D E) =
  add_PP (mult_PP (k'0 * k) (vec A B)) (mult_PP (k'0 * k') (vec A C)));
 intros.
cut
 (add_PP (mult_PP k (vec D F)) (mult_PP (- k0) (vec D E)) =
  mult_PP (k * k'0 + - (k0 * k')) (vec A C)); intros.
cut
 (add_PP (mult_PP k' (vec D F)) (mult_PP (- k'0) (vec D E)) =
  mult_PP (k' * k0 + - (k'0 * k)) (vec A B)); intros.
elim (classic (k * k'0 + - (k0 * k') = 0)); intros.
cut (k' * k0 + - (k'0 * k) = 0); intros.
rewrite H15 in H13.
rewrite H14 in H12.
elim (classic (k = 0)); intros.
rewrite H16 in H15.
rewrite H16 in H9.
elim (classic (k' = 0)); intros.
rewrite H17 in H9.
absurd (D = E); auto with geo.
apply conversion_PP with (a := 1) (b := 1); auto with *.
unfold vec in H9.
RingPP2 H9; RingPP.
cut (k0 = 0); intros.
clear H10; clear H8.
rewrite H18 in H11.
elim (classic (k'0 = 0)); intros.
rewrite H8 in H11.
absurd (D = F).
apply non_alignes_distincts with E; auto.
apply conversion_PP with (a := 1) (b := 1); auto with *.
unfold vec in H11.
RingPP2 H11; RingPP.
absurd (alignes D E F); auto.
apply colineaire_alignes with (k'0 * / k'); auto.
rewrite H11; rewrite H9.
unfold vec in |- *.
FieldPP k'.
cut (k' * k0 = 0); intros.
RReplace k0 (/ k' * (k' * k0)).
rewrite H18; field; auto.
field; auto.
rewrite <- H15; ring.
absurd (alignes D E F); auto.
apply colineaire_alignes with (/ k * k0); auto.
cut (mult_PP k (vec D F) = mult_PP k0 (vec D E)); intros.
apply mult_PP_regulier with k; auto.
rewrite H17.
FieldPP k.
VReplace (mult_PP k0 (vec D E))
 (add_PP (mult_PP k0 (vec D E)) (mult_PP 0 (vec A C))).
rewrite <- H12; RingPP.
RReplace (k' * k0 + - (k'0 * k)) (- (k * k'0 + - (k0 * k'))).
rewrite H14; ring.
cut (k' * k0 + - (k'0 * k) <> 0); intros.
split; [ try assumption | idtac ].
exists (/ (k' * k0 + - (k'0 * k)) * - k'0);
 exists (/ (k' * k0 + - (k'0 * k)) * k').
apply mult_PP_regulier with (k' * k0 + - (k'0 * k)); auto.
rewrite <- H13.
FieldPP (k' * k0 + - (k'0 * k)).
exists (/ (k * k'0 + - (k0 * k')) * - k0);
 exists (/ (k * k'0 + - (k0 * k')) * k).
apply mult_PP_regulier with (k * k'0 + - (k0 * k')); auto with real.
rewrite <- H12.
FieldPP (k * k'0 + - (k0 * k')).
RReplace (k' * k0 + - (k'0 * k)) (- (k * k'0 + - (k0 * k'))).
auto with real.
replace (mult_PP (- k'0) (vec D E)) with
 (add_PP (mult_PP (- k'0 * k) (vec A B)) (mult_PP (- k'0 * k') (vec A C))).
rewrite H11; RingPP.
apply mult_PP_regulier with (-1); auto with real.
VReplace (mult_PP (-1) (mult_PP (- k'0) (vec D E))) (mult_PP k'0 (vec D E)).
rewrite H7; RingPP.
replace (mult_PP (- k0) (vec D E)) with
 (add_PP (mult_PP (- k0 * k) (vec A B)) (mult_PP (- k0 * k') (vec A C))).
rewrite H4; RingPP.
apply mult_PP_regulier with (-1); auto with real.
VReplace (mult_PP (-1) (mult_PP (- k0) (vec D E))) (mult_PP k0 (vec D E)).
rewrite H6; RingPP.
rewrite H9; RingPP.
rewrite H9; RingPP.
rewrite H11; RingPP.
rewrite H11; RingPP.
apply non_alignes_distincts with E; auto.
auto with geo.
Qed.
 
Lemma para_plan_trans :
 forall A B C D E F G H I : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 ~ alignes G H I ->
 para_plan_plan (plan A B C) (plan D E F) ->
 para_plan_plan (plan D E F) (plan G H I) ->
 para_plan_plan (plan A B C) (plan G H I).
intros A B C D E F G H I H0 H1 H2 H3 H4; try assumption.
deroule_triangle A B C.
deroule_triangle D E F.
deroule_triangle G H I.
elim
 def_para_plan_plan2
  with (A := A) (B := B) (C := C) (D := D) (E := E) (F := F);
 [ intros H14 H15; try clear def_para_plan_plan2; auto | auto | auto | auto ].
elim
 def_para_plan_plan2
  with (A := D) (B := E) (C := F) (D := G) (E := H) (F := I);
 [ intros; auto | auto | auto | auto ].
elim
 def_para_plan_plan2
  with (A := D) (B := E) (C := F) (D := G) (E := H) (F := I);
 [ try clear def_para_plan_plan2; auto | auto | auto | auto ].
intros.
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros k H20; elim H20; [ intros k' H21; try clear H20; auto ]
 | auto
 | auto
 | auto ].
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros k0 H22; elim H22; [ intros k'0 H23; try clear H22; auto ]
 | auto
 | auto
 | auto ].
elim para_plan_dr_vecteur with (A := D) (B := E) (C := F) (D := G) (E := H);
 [ intros k1 H20; elim H20; [ intros k'1 H22; try clear H20; auto ]
 | auto
 | auto
 | auto ].
elim para_plan_dr_vecteur with (A := D) (B := E) (C := F) (D := G) (E := I);
 [ intros k2 H20; elim H20; [ intros k'2 H24; try clear H20; auto ]
 | auto
 | auto
 | auto ].
cut
 (ex
    (fun a : R =>
     ex
       (fun b : R =>
        vec G I = add_PP (mult_PP a (vec A B)) (mult_PP b (vec A C)))) /\
  ex
    (fun c : R =>
     ex
       (fun d : R =>
        vec G H = add_PP (mult_PP c (vec A B)) (mult_PP d (vec A C)))));
 intros.
elim H20;
 [ intros H25 H26; elim H25;
    [ intros a H27; elim H27;
       [ intros b H28; try clear H27 H25 H20; try exact H28 ] ] ].
elim H26;
 [ intros c H20; elim H20; [ intros d H25; try clear H20 H26; try exact H25 ] ].
apply couple_vecteurs_coplanaires with (a := c) (b := d) (c := a) (d := b);
 auto.
split; [ try assumption | idtac ].
cut
 (vec G I =
  add_PP (mult_PP k2 (add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C))))
    (mult_PP k'2 (add_PP (mult_PP k0 (vec A B)) (mult_PP k'0 (vec A C)))));
 intros.
exists (k2 * k + k'2 * k0).
exists (k2 * k' + k'2 * k'0).
rewrite H20; RingPP.
rewrite <- H21; rewrite <- H23; rewrite H24; auto.
cut
 (vec G H =
  add_PP (mult_PP k1 (add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C))))
    (mult_PP k'1 (add_PP (mult_PP k0 (vec A B)) (mult_PP k'0 (vec A C)))));
 intros.
exists (k1 * k + k'1 * k0).
exists (k1 * k' + k'1 * k'0).
rewrite H20; RingPP.
rewrite <- H21; rewrite <- H23; rewrite H22; auto.
Qed.
 
Lemma plans_paralleles_ou_droite_incluse2 :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 para_plan_plan (plan A B C) (plan D E F) \/
 (exists I : PO,
    (exists J : PO,
       I <> J :>PO /\
       incluse (droite I J) (plan A B C) /\ incluse (droite I J) (plan D E F))).
intros A B C D E F H H0; try assumption.
deroule_triangle D E F.
elim
 position_relative_droite_plan
  with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros H4; try clear position_relative_droite_plan
 | intros H4; try clear position_relative_droite_plan; try exact H4
 | try trivial
 | try trivial ].
elim
 position_relative_droite_plan
  with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros H5; try clear position_relative_droite_plan
 | intros H5; try clear position_relative_droite_plan; try exact H5
 | try trivial
 | try trivial ].
left; try assumption.
apply def_para_plan_plan; auto.
elim H5; intros.
elim def_contact2 with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros J H8; elim H8;
    [ intros H9 H10; try clear H8 def_contact2; try exact H10 ]
 | try trivial
 | try trivial
 | try trivial ].
right; try assumption.
elim existence_representant_vecteur with (A := J) (B := E) (C := D); intros I;
 intros; try clear existence_representant_vecteur.
exists I; exists J.
cut (I <> J).
intros H30.
split; [ trivial | split; [ idtac | try assumption ] ].
cut (para_plan_dr (plan A B C) (droite J I)); intros.
apply droite_incluse_plan2; auto.
apply paralleles_droite_plan_coplanaires_incluse with (3 := H12); auto.
apply paralleles_droites_plan_trans with (4 := H4); auto.
apply def_paralleles with (-1); auto.
unfold vec in H11.
VReplace (cons (-1) I) (mult_PP (-1) (cons 1 I)).
RingPP2 H11.
Ringvec.
cut (coplanaires D E F J).
intros H20.
apply droite_incluse_plan2; auto.
cut (para_plan_dr (plan D E F) (droite J I)); intros.
apply paralleles_droite_plan_coplanaires_incluse with (3 := H12); auto.
apply def_para_plan_dr with (D := D) (E := E); auto with geo.
apply def_paralleles with (-1); auto.
unfold vec in H11.
VReplace (cons (-1) I) (mult_PP (-1) (cons 1 I)).
RingPP2 H11.
Ringvec.
unfold coplanaires in |- *.
hPPalignes H9 ipattern:k.
right; try assumption.
exists k; exists 0.
rewrite H9; RingPP.
unfold vec in H11.
unfold not in |- *; intros; apply H3.
apply conversion_PP with (a := 1) (b := 1); auto.
cut (add_PP (cons (-1) E) (cons 1 D) = add_PP (cons (-1) J) (cons 1 I));
 intros; auto.
RingPP2 H13.
rewrite H12; RingPP.
auto with *.
elim
 position_relative_droite_plan
  with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros H5; try clear position_relative_droite_plan
 | unfold perce in |- *; intros H5; try clear position_relative_droite_plan;
    try exact H5
 | try trivial
 | try trivial ].
elim def_contact2 with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros J H6; elim H6;
    [ intros H7 H8; try clear H6 def_contact2; try exact H8 ]
 | try trivial
 | try trivial
 | try trivial ].
right; try assumption.
elim existence_representant_vecteur with (A := J) (B := D) (C := F); intros I;
 intros; try clear existence_representant_vecteur; 
 try exact H5.
exists I; exists J.
cut (I <> J).
intros H30.
split; [ trivial | split; [ idtac | try assumption ] ].
cut (para_plan_dr (plan A B C) (droite J I)); intros.
apply droite_incluse_plan2; auto.
apply paralleles_droite_plan_coplanaires_incluse with (3 := H10); auto.
apply paralleles_droites_plan_trans with (4 := H5); auto.
apply def_paralleles with 1; auto.
unfold vec in H9; auto.
RingPP2 H9.
RingPP.
cut (coplanaires D E F J); auto with geo.
intros H20.
apply droite_incluse_plan2; auto.
cut (para_plan_dr (plan D E F) (droite J I)); intros.
apply paralleles_droite_plan_coplanaires_incluse with (3 := H10);
 auto with geo.
apply def_para_plan_dr with (D := D) (E := F); auto with geo.
apply def_paralleles with 1; auto.
unfold vec in H9.
RingPP2 H9.
RingPP.
unfold vec in H9.
unfold not in |- *; intros; apply H1.
apply conversion_PP with (a := 1) (b := 1); auto.
cut (add_PP (cons (-1) F) (cons 1 D) = add_PP (cons 1 J) (cons (-1) I));
 intros; auto.
RingPP2 H11.
rewrite H10; RingPP.
VReplace (cons (-1) I) (mult_PP (-1) (cons 1 I)).
RingPP2 H9.
RingPP.
auto with *.
unfold perce in H4.
elim H4; [ intros H6 H7; try clear H4; try exact H7 ].
elim def_contact2 with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros J H6; elim H6; [ intros H7 H8; try clear H6; try exact H8 ]
 | trivial
 | trivial
 | trivial ].
elim def_contact2 with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros I H6; elim H6; [ intros H9 H10; try clear H6; try exact H10 ]
 | trivial
 | trivial
 | trivial ].
right.
elim (classic (I = J)); intros.
cut (I = D); intros.
elim
 position_relative_droite_plan
  with (A := A) (B := B) (C := C) (D := E) (E := F);
 [ intros H12; try clear position_relative_droite_plan
 | unfold perce in |- *; intros H12; try clear position_relative_droite_plan;
    trivial
 | trivial
 | trivial ].
elim existence_representant_vecteur with (A := I) (B := E) (C := F);
 intros K H13; try clear existence_representant_vecteur.
cut (E <> F); intros.
cut (I <> K); intros.
exists I; exists K.
split; [ trivial | split; [ idtac | try assumption ] ].
apply droite_incluse_plan2; auto with geo.
cut (para_plan_dr (plan A B C) (droite I K)); intros.
apply paralleles_droite_plan_coplanaires_incluse with (3 := H16);
 auto with geo.
apply paralleles_droites_plan_trans with (4 := H12); auto with geo.
apply def_paralleles with 1; auto.
unfold vec in H13.
RingPP2 H13.
RingPP.
apply droite_incluse_plan2; auto with geo.
apply paralleles_droite_plan_coplanaires_incluse with (D := I) (E := K);
 auto with geo.
apply def_para_plan_dr with (D := E) (E := F); auto with geo.
apply def_paralleles with 1; auto.
unfold vec in H13.
RingPP2 H13.
RingPP.
unfold not in |- *; intros; apply H14.
apply conversion_PP with (a := 1) (b := 1); auto.
unfold vec in H12.
cut (add_PP (cons (-1) E) (cons 1 F) = add_PP (cons (-1) I) (cons 1 K));
 intros; auto.
RingPP2 H16.
rewrite H15; RingPP.
auto with *.
unfold not in |- *; intros; apply H0.
rewrite H14; auto with geo.
elim H12; [ intros H13 H14; try clear H12; try exact H14 ].
elim def_contact2 with (A := A) (B := B) (C := C) (D := E) (E := F);
 [ intros K H12; try clear def_perce2; try exact H8
 | trivial
 | trivial
 | trivial ].
elim H12; [ intros H15 H16; try clear H12; try exact H16 ].
exists I; exists K.
cut (I <> K); intros.
split; [ trivial | split; [ idtac | try assumption ] ].
apply droite_incluse_plan2; auto.
apply droite_incluse_plan2; auto.
rewrite H11; auto with geo.
auto with geo.
rewrite H11; auto.
unfold not in |- *; intros; apply H0.
rewrite H12; auto with geo.
apply concours_unique with (A := D) (A1 := E) (B := F) (B1 := D);
 auto with geo.
rewrite H6; auto.
exists I; exists J.
split; [ trivial | split; [ idtac | try assumption ] ].
apply droite_incluse_plan2; auto.
apply droite_incluse_plan2; auto.
auto with geo.
auto with geo.
elim H5; [ intros H6 H9; try clear H5; try exact H9 ].
elim H4; auto.
Qed.