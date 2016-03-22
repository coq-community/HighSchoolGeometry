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


Require Export Plans_paralleles.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter secants : PL -> PL -> Prop.
 
Axiom
  def_secants :
    forall A B C D E F I J : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    I <> J ->
    incluse (droite I J) (plan A B C) ->
    incluse (droite I J) (plan D E F) ->
    ~ para_plan_plan (plan A B C) (plan D E F) ->
    secants (plan A B C) (plan D E F).
 
Axiom
  def_secants2 :
    forall A B C D E F : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    secants (plan A B C) (plan D E F) ->
    ~ para_plan_plan (plan A B C) (plan D E F) /\
    (exists I : PO,
       (exists J : PO,
          I <> J /\
          incluse (droite I J) (plan A B C) /\
          incluse (droite I J) (plan D E F))).
 
Theorem position_relative_plans :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 para_plan_plan (plan A B C) (plan D E F) \/
 secants (plan A B C) (plan D E F).
intros.
lapply
 (plans_paralleles_ou_droite_incluse2 (A:=A) (B:=B) (C:=C) (D:=D) (E:=E)
    (F:=F)); intros; auto.
elim H1;
 [ intros H2; try clear H1
 | intros H2; elim H2;
    [ intros I H3; elim H3;
       [ intros J H4; elim H4;
          [ intros H5 H6; elim H6;
             [ intros H7 H8; try clear H6 H4 H3 H2 H1; try trivial ] ] ] ]
 | try trivial ].
left; try assumption.
elim (classic (para_plan_plan (plan A B C) (plan D E F))); intros.
left; try assumption.
right; try assumption.
apply def_secants with (I := I) (J := J); auto.
Qed.
 
Theorem toit :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 paralleles (droite D E) (droite A B) ->
 ~ para_plan_plan (plan A B C) (plan D E F) ->
 exists I : PO,
   (exists J : PO,
      (I <> J :>PO /\ paralleles (droite A B) (droite I J)) /\
      incluse (droite I J) (plan A B C) /\ incluse (droite I J) (plan D E F)).
intros.
deroule_triangle A B C.
deroule_triangle D E F.
elim
 position_relative_droite_plan
  with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros H9; try clear position_relative_droite_plan
 | unfold perce in |- *; intros H9; try clear position_relative_droite_plan;
    try exact H9
 | try trivial
 | trivial ].
2: elim H9; [ intros H10 H11; try clear H9; try exact H11 ].
absurd (para_plan_plan (plan A B C) (plan D E F)); auto.
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros k H10; elim H10;
    [ intros k' H11; try clear H10 para_plan_dr_vecteur; auto ]
 | auto
 | auto
 | auto ].
elim paralleles_vecteur with (A := D) (B := E) (C := A) (D := B);
 [ intros k0 H12; try clear paralleles_vecteur; auto | auto | auto | auto ].
apply couple_vecteurs_coplanaires with (a := k0) (b := 0) (c := k) (d := k');
 auto.
rewrite H12; RingPP.
elim def_contact2 with (A := A) (B := B) (C := C) (D := D) (E := F);
 [ intros I H12; try clear def_secants2 | trivial | trivial | trivial ].
elim H12; [ intros H9 H13; try clear H12; try exact H13 ].
exists I.
elim existence_representant_vecteur with (A := I) (B := A) (C := B);
 intros J H14; try clear existence_representant_vecteur.
exists J.
cut (I <> J).
intros H21.
cut (paralleles (droite A B) (droite I J)).
intros H16; try assumption.
split; [ split; [ try assumption | idtac ] | idtac ].
try exact H16.
split; [ try assumption | idtac ].
apply droite_incluse_plan2; auto.
apply paralleles_droite_plan_coplanaires_incluse with (D := I) (E := J); auto.
apply def_para_plan_dr with (D := A) (E := B); auto with geo.
cut (coplanaires D E F I).
intros H22.
apply droite_incluse_plan2; auto.
cut (paralleles (droite D E) (droite I J)); intros.
apply paralleles_droite_plan_coplanaires_incluse with (D := I) (E := J); auto.
apply def_para_plan_dr with (D := D) (E := E); auto with geo.
apply paralleles_trans with (5 := H16); auto.
auto with geo.
apply colineaires_paralleles with 1; auto.
rewrite H14; RingPP.
unfold not in |- *; intros; apply H5.
apply conversion_PP with (a := 1) (b := 1); auto with *.
cut (vec A B = vec I J); intros.
unfold vec in H15.
RingPP2 H15.
rewrite H12; RingPP.
rewrite H14; auto.
Qed.
 
Lemma plans_paralleles_droite :
 forall A B C D E F I J : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 I <> J ->
 para_plan_plan (plan A B C) (plan D E F) ->
 para_plan_dr (plan A B C) (droite I J) ->
 para_plan_dr (plan D E F) (droite I J).
intros.
deroule_triangle A B C.
deroule_triangle D E F.
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := I) (E := J);
 [ intros k H10; elim H10; [ intros k' H11; try clear H10; try exact H11 ]
 | auto
 | auto
 | auto ].
elim
 plans_paralleles_vecteurs
  with (A := D) (B := E) (C := F) (D := A) (E := B) (F := C); 
 auto.
intros H10 H12; try assumption.
elim H12;
 [ intros c H13; elim H13; [ intros d H14; try clear H13 H12; try exact H14 ] ].
elim H10;
 [ intros a H12; elim H12; [ intros b H13; try clear H12 H10; try exact H13 ] ].
cut
 (vec I J =
  add_PP (mult_PP k (add_PP (mult_PP a (vec D E)) (mult_PP b (vec D F))))
    (mult_PP k' (add_PP (mult_PP c (vec D E)) (mult_PP d (vec D F)))));
 intros.
apply vecteurs_para_plan_dr with (k := k * a + k' * c) (k' := k * b + k' * d);
 auto.
rewrite H10; RingPP.
rewrite H11; rewrite H14; rewrite H13; RingPP.
apply para_plan_sym; auto.
Qed.
 
Lemma plans_paralleles_secants_droites_paralleles :
 forall A B C D E F I J K : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 ~ alignes I J K ->
 para_plan_plan (plan A B C) (plan D E F) ->
 ~ para_plan_plan (plan A B C) (plan I J K) ->
 incluse (droite I J) (plan A B C) ->
 ex
   (fun G : PO =>
    ex
      (fun L : PO =>
       (G <> L /\ incluse (droite G L) (plan I J K)) /\
       incluse (droite G L) (plan D E F) /\
       paralleles (droite G L) (droite I J))).
intros.
deroule_triangle A B C.
deroule_triangle D E F.
deroule_triangle I J K.
cut (para_plan_dr (plan D E F) (droite I J)); intros.
elim
 position_relative_droite_plan
  with (A := D) (B := E) (C := F) (D := I) (E := K);
 [ intros H15; try clear position_relative_droite_plan
 | unfold perce in |- *; intros H15; try clear position_relative_droite_plan;
    try exact H15
 | try trivial
 | try trivial ].
2: elim H15; [ intros H16 H17; try clear H15; try exact H17 ].
cut (para_plan_plan (plan D E F) (plan I J K)); intros.
absurd (para_plan_plan (plan A B C) (plan I J K)); auto.
apply para_plan_trans with (D := D) (E := E) (F := F); auto.
apply def_para_plan_plan; auto.
elim def_contact2 with (3 := H17);
 [ intros G H15; elim H15; intros; try clear H15; auto | auto | auto ].
elim existence_representant_vecteur with (A := G) (B := I) (C := J);
 intros L H20; try clear existence_representant_vecteur.
exists G; exists L.
cut (G <> L); intros.
cut (paralleles (droite G L) (droite I J)); intros.
split; [ split; [ try assumption | idtac ] | idtac ].
cut (coplanaires I J K G); intros.
apply droite_incluse_plan2; auto with geo.
apply paralleles_droite_plan_coplanaires_incluse with (D := G) (E := L); auto.
apply vecteurs_para_plan_dr with (k := 1) (k' := 0); auto.
rewrite H20; RingPP.
auto with geo.
split; [ try assumption | auto ].
cut (para_plan_dr (plan D E F) (droite G L)); intros.
apply droite_incluse_plan2; auto with geo.
apply paralleles_droite_plan_coplanaires_incluse with (D := G) (E := L); auto.
apply paralleles_droites_plan_trans with (D := I) (E := J); auto with geo.
apply colineaires_paralleles with 1; auto with geo.
rewrite H20; RingPP.
unfold not in |- *; intros; apply H13.
apply conversion_PP with (a := 1) (b := 1); auto with *.
cut (vec I J = vec G L); intros.
unfold vec in H21.
RingPP2 H21.
rewrite H15; RingPP.
rewrite H20; auto.
apply plans_paralleles_droite with (4 := H2); auto.
apply paralleles_droite_incluse; auto.
Qed.
Parameter disjoints : PL -> PL -> Prop.
Parameter confondus : PL -> PL -> Prop.
 
Axiom
  def_disjoints :
    forall A B C D E F : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    (forall I : PO, ~ (coplanaires A B C I /\ coplanaires D E F I)) ->
    disjoints (plan A B C) (plan D E F).
 
Axiom
  def_disjoints2 :
    forall A B C D E F : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    disjoints (plan A B C) (plan D E F) ->
    forall I : PO, ~ (coplanaires A B C I /\ coplanaires D E F I).
 
Axiom
  def_confondus :
    forall A B C D E F : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    (forall I : PO, coplanaires A B C I -> coplanaires D E F I) ->
    confondus (plan A B C) (plan D E F).
 
Axiom
  def_confondus2 :
    forall A B C D E F : PO,
    ~ alignes A B C ->
    ~ alignes D E F ->
    confondus (plan A B C) (plan D E F) ->
    forall I : PO, coplanaires A B C I -> coplanaires D E F I.
 
Lemma non_disjoints_exists :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 ~ disjoints (plan A B C) (plan D E F) ->
 exists I : PO, coplanaires A B C I /\ coplanaires D E F I.
intros A B C D E F H H0 H1; try assumption.
cut (~ (forall I : PO, ~ (coplanaires A B C I /\ coplanaires D E F I)));
 intros.
elim
 not_all_not_ex
  with
    (U := PO)
    (P := fun I : PO => coplanaires A B C I /\ coplanaires D E F I);
 [ intros I H3; try clear not_all_not_ex; try exact H3 | auto ].
exists I; auto.
red in |- *; (intros; apply H1).
apply def_disjoints; auto.
Qed.
 
Theorem position_relative_plans_paralleles :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 para_plan_plan (plan A B C) (plan D E F) ->
 disjoints (plan A B C) (plan D E F) \/ confondus (plan A B C) (plan D E F).
intros A B C D E F H H0 H3; try assumption.
intros.
assert (A <> B); auto with geo.
assert (D <> E); auto with geo.
elim (classic (disjoints (plan A B C) (plan D E F))); intros.
left; try assumption.
right; try assumption.
elim non_disjoints_exists with (3 := H4);
 [ intros I H5; try clear non_disjoints_exists; try exact H3 | auto | auto ].
elim H5; [ intros H6 H7; try clear H5; try exact H6 ].
apply def_confondus; auto.
intros J H5; try assumption.
elim
 plans_paralleles_vecteurs
  with (A := D) (B := E) (C := F) (D := A) (E := B) (F := C); 
 auto.
intros.
elim H9; intros c H10; elim H10; intros d H11; try clear H10 H9;
 try exact H11.
elim H8; intros a H9; elim H9; intros b H10; try clear H9 H8; try exact H10.
hcoplanaires H5 ipattern:x ipattern:k'.
hcoplanaires H6 ipattern:x0 ipattern:k'0.
hcoplanaires H7 ipattern:x1 ipattern:k'1.
apply
 (vecteur_def_coplanaires
    (k:=x1 + -1 * (x0 * a + k'0 * c) + (x * a + k' * c))
    (k':=k'1 + -1 * (x0 * b + k'0 * d) + (x * b + k' * d))).
replace (vec D J) with
 (add_PP (add_PP (vec D I) (mult_PP (-1) (vec A I))) (vec A J)).
rewrite H7.
rewrite H6.
rewrite H5.
rewrite H10.
rewrite H11.
Ringvec.
Ringvec.
apply para_plan_sym; auto.
Qed.
 
Theorem position_relative_plans_general :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 (disjoints (plan A B C) (plan D E F) \/ confondus (plan A B C) (plan D E F)) \/
 secants (plan A B C) (plan D E F).
intros.
assert (A <> B); auto with geo.
assert (D <> E); auto with geo.
elim (classic (para_plan_plan (plan A B C) (plan D E F))); intros.
left; try assumption.
apply position_relative_plans_paralleles; auto.
right; try assumption.
elim
 position_relative_plans
  with (A := A) (B := B) (C := C) (D := D) (E := E) (F := F);
 [ intros H4; try clear position_relative_plans
 | intros H4; try clear position_relative_plans; auto
 | auto
 | auto ].
tauto.
Qed.
 
Theorem position_relative_plans_non_disjoints :
 forall A B C D E F : PO,
 ~ alignes A B C ->
 ~ alignes D E F ->
 ~ disjoints (plan A B C) (plan D E F) ->
 secants (plan A B C) (plan D E F) \/ confondus (plan A B C) (plan D E F).
intros.
elim
 position_relative_plans_general
  with (A := A) (B := B) (C := C) (D := D) (E := E) (F := F);
 [ intros H2; elim H2;
    [ intros H3; try clear H2 position_relative_plans_general
    | intros H3; try clear H2 position_relative_plans_general; try exact H3 ]
 | intros H2
 | auto
 | auto ].
elim H2; [ intros H4; try clear H2 | intros H4; try clear H2; try exact H4 ].
tauto.
right; try assumption.
elim H2; [ intros H4; try clear H2; try exact H4 | intros H4; try clear H2 ].
tauto.
right; try assumption.
left; try assumption.
Qed.