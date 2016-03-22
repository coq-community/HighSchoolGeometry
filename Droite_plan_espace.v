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


Require Export Droite_espace.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter PL : Type.
Parameter incluse : DR -> PL -> Prop.
Parameter plan : PO -> PO -> PO -> PL.
Parameter para_plan_dr : PL -> DR -> Prop.
 
Axiom
  droite_incluse_plan :
    forall A B C D E : PO,
    D <> E ->
    ~ alignes A B C ->
    incluse (droite D E) (plan A B C) ->
    coplanaires A B C D /\ coplanaires A B C E.
 
Axiom
  droite_incluse_plan2 :
    forall A B C D E : PO,
    D <> E ->
    ~ alignes A B C ->
    coplanaires A B C D ->
    coplanaires A B C E -> incluse (droite D E) (plan A B C).
 
Axiom
  coplanaire_trans3 :
    forall A B C D E F G : PO,
    ~ alignes A B C ->
    coplanaires A B C D ->
    coplanaires A B C E ->
    coplanaires A B C F -> coplanaires A B C G -> coplanaires D E F G.
 
Lemma droites_coplanaires :
 forall A B C D E F G : PO,
 D <> E ->
 F <> G ->
 ~ alignes A B C ->
 incluse (droite D E) (plan A B C) ->
 incluse (droite F G) (plan A B C) ->
 concours (droite D E) (droite F G) \/ paralleles (droite D E) (droite F G).
intros A B C D E F G H10 H11 H H0 H1; try assumption.
intros.
elim (classic (paralleles (droite D E) (droite F G))); intros; auto.
left; try assumption.
elim droites_non_paralleles with (3 := H2); intros; auto.
absurd (coplanaires F G D E); auto.
elim droite_incluse_plan with (3 := H1); intros; auto.
elim droite_incluse_plan with (3 := H0); intros; auto.
apply coplanaire_trans3 with (A := A) (B := B) (C := C); auto.
Qed.
 
Axiom
  def_para_plan_dr :
    forall A B C D E F G : PO,
    ~ alignes A B C ->
    D <> E ->
    F <> G ->
    coplanaires A B C D ->
    coplanaires A B C E ->
    paralleles (droite D E) (droite F G) ->
    para_plan_dr (plan A B C) (droite F G).
 
Axiom
  def_para_plan_dr2 :
    forall A B C F G : PO,
    ~ alignes A B C ->
    F <> G ->
    para_plan_dr (plan A B C) (droite F G) ->
    exists D : PO,
      (exists E : PO,
         (coplanaires A B C D /\ coplanaires A B C E) /\
         D <> E /\ paralleles (droite D E) (droite F G)).
 
Lemma paralleles_droites_plan :
 forall A B C D E : PO,
 ~ alignes A B C ->
 A <> B ->
 D <> E ->
 paralleles (droite A B) (droite D E) ->
 para_plan_dr (plan A B C) (droite D E).
intros.
apply def_para_plan_dr with (D := A) (E := B); auto with geo.
Qed.
 
Lemma paralleles_droite_incluse :
 forall A B C D E : PO,
 ~ alignes A B C ->
 D <> E ->
 incluse (droite D E) (plan A B C) -> para_plan_dr (plan A B C) (droite D E).
intros.
elim droite_incluse_plan with (A := A) (B := B) (C := C) (D := D) (E := E);
 intros; auto.
apply def_para_plan_dr with (D := D) (E := E); auto with geo.
Qed.
 
Lemma paralleles_droite_plan_coplanaires_incluse :
 forall A B C D E : PO,
 D <> E :>PO ->
 ~ alignes A B C ->
 para_plan_dr (plan A B C) (droite D E) ->
 coplanaires A B C D -> coplanaires A B C E.
intros A B C D E H20 H H0 H1.
unfold coplanaires in |- *.
hPPcoplanaires H1 ipattern:a1 ipattern:b1.
elim def_para_plan_dr2 with (3 := H0); auto.
intros F H2; elim H2; intros G H3; elim H3; intros H4 H5; elim H5;
 intros H6 H7; try clear H5 H3 H2; try exact H7.
elim H4; [ intros H2 H3; try clear H4; try exact H3 ].
hPPcoplanaires H2 ipattern:a ipattern:b.
hPPcoplanaires H3 ipattern:a0 ipattern:b0.
cut (paralleles (droite D E) (droite F G)); intros; auto with geo.
elim def_paralleles2 with (3 := H4); auto; intros.
right; try assumption.
exists (x * a0 + (- x * a + a1)).
exists (x * b0 + (- x * b + b1)).
RingPP1 H5.
VReplace (cons x G) (mult_PP x (cons 1 G)).
VReplace (cons (- x) F) (mult_PP (- x) (cons 1 F)).
VReplace (mult_PP (-1) (cons (-1) D)) (cons 1 D).
rewrite H1; rewrite H3; rewrite H2.
RingPP.
Qed.
 
Lemma paralleles_plan_droite_non_secants :
 forall A B C D E : PO,
 D <> E ->
 ~ alignes A B C ->
 para_plan_dr (plan A B C) (droite D E) ->
 ~ coplanaires A B C D ->
 ~ (exists I : PO, alignes D E I /\ coplanaires A B C I).
intros.
unfold not in |- *; intros.
elim H3; intros I H4; elim H4; intros H5 H6; try clear H4 H3; try exact H6.
elim def_para_plan_dr2 with (3 := H1); auto.
intros F H3; elim H3; intros G H4; elim H4; intros H7 H8; elim H8;
 intros H9 H10; try clear H8 H4 H3; try exact H10.
apply H2.
cut (I <> D); intros.
cut (para_plan_dr (plan A B C) (droite I D)); intros.
apply paralleles_droite_plan_coplanaires_incluse with (3 := H4); auto.
apply def_para_plan_dr with (D := F) (E := G); auto.
elim H7; intros H13 H4; try clear H7; try exact H13.
elim H7; intros H13 H4; try clear H7; try exact H4.
apply paralleles_trans with D E; auto.
generalize (alignes_paralleles (A:=D) (B:=E) (C:=I)); intros.
apply paralleles_trans with D I; auto with geo.
unfold not in |- *; intros; apply H2.
rewrite <- H3; auto.
Qed.
Parameter contact : DR -> PL -> Prop.
 
Axiom
  def_contact :
    forall A B C D E I : PO,
    D <> E ->
    ~ alignes A B C ->
    alignes D E I -> coplanaires A B C I -> contact (droite D E) (plan A B C).
 
Axiom
  def_contact2 :
    forall A B C D E : PO,
    D <> E ->
    ~ alignes A B C ->
    contact (droite D E) (plan A B C) ->
    exists I : PO, alignes D E I /\ coplanaires A B C I.
 
Definition perce (d : DR) (P : PL) := ~ incluse d P /\ contact d P.
 
Lemma position_relative_plan_droite_paralleles :
 forall A B C D E : PO,
 D <> E ->
 ~ alignes A B C ->
 para_plan_dr (plan A B C) (droite D E) ->
 incluse (droite D E) (plan A B C) \/ ~ contact (droite D E) (plan A B C).
intros.
elim (classic (coplanaires A B C D)); intros.
left; try assumption.
apply droite_incluse_plan2; auto.
apply paralleles_droite_plan_coplanaires_incluse with D; auto.
right; try assumption.
generalize
 (paralleles_plan_droite_non_secants (A:=A) (B:=B) (C:=C) (D:=D) (E:=E));
 intros H7.
unfold not in |- *; intros.
elim H7; try assumption.
apply def_contact2; auto.
Qed.
 
Lemma para_plan_dr_vecteur :
 forall A B C D E : PO,
 D <> E :>PO ->
 ~ alignes A B C ->
 para_plan_dr (plan A B C) (droite D E) ->
 exists k : R,
   (exists k' : R,
      vec D E = add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C))).
intros A B C D E H30 H H0; unfold vec in |- *.
elim def_para_plan_dr2 with (A := A) (B := B) (C := C) (F := D) (G := E);
 [ intros F H2; elim H2; intros G H3; try clear H2; try exact H3
 | auto
 | auto
 | auto ].
elim H3; intros H2 H4; elim H4; intros H5 H6; try clear H4 H3; try exact H6.
elim H2; [ intros H1 H3; try clear H2; try exact H3 ].
hPPcoplanaires H1 ipattern:a0 ipattern:b0.
hPPcoplanaires H3 ipattern:a1 ipattern:b1.
generalize (def_paralleles2 (A:=D) (B:=E) (C:=F) (D:=G)); intros H9.
elim H9;
 [ intros k H2; try clear H9; try exact H1
 | auto with geo
 | auto with geo
 | auto with geo ].
replace (add_PP (cons (-1) D) (cons 1 E)) with
 (add_PP (cons 1 E) (cons (-1) D)).
rewrite H2.
replace (cons k G) with (mult_PP k (cons 1 G)).
replace (cons (- k) F) with (mult_PP (- k) (cons 1 F)).
rewrite H3.
rewrite H1.
exists (k * (b1 + - b0)); exists (k * (a0 + b0 + - (a1 + b1))).
RingPP.
RingPP.
RingPP.
RingPP.
Qed.
 
Lemma vecteurs_para_plan_dr :
 forall (A B C D E : PO) (k k' : R),
 D <> E ->
 ~ alignes A B C ->
 vec D E = add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C)) ->
 para_plan_dr (plan A B C) (droite D E).
intros.
cut
 (ex
    (fun F : PO =>
     vec A F = add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C)))); 
 intros.
elim H2; intros F H3; try clear H2; try exact H3.
cut (vec A F = vec D E); intros.
cut (A <> F).
intros H30.
apply def_para_plan_dr with (D := A) (E := F); auto with geo.
unfold vec in H2.
apply vecteur_def_coplanaires with (1 := H3); auto with geo.
apply colineaires_paralleles with 1; auto with geo.
rewrite H2; Ringvec.
unfold not in |- *; intros; apply H.
apply conversion_PP with (a := 1) (b := 1); auto with *.
cut (vec D E = vec A F); intros.
RingPP2 H5.
rewrite H4.
unfold vec in |- *.
RingPP.
auto with *.
rewrite H3; auto.
elim (classic (k' = - k)); intros.
rewrite H2.
replace (add_PP (mult_PP k (vec A B)) (mult_PP (- k) (vec A C))) with
 (mult_PP k (vec C B)).
elim
 existence_representant_mult_vecteur with (A := A) (B := C) (C := B) (k := k);
 intros D0 H3; try clear existence_representant_mult_vecteur; 
 try exact H3.
exists D0; auto.
unfold vec in |- *; RingPP.
exists
 (barycentre (cons (1 + - (k + k')) A)
    (cons (k + k') (barycentre (cons k B) (cons k' C)))).
unfold vec in |- *.
pattern 1 at 2 in |- *.
replace 1 with (1 + - (k + k') + (k + k')).
repeat rewrite <- add_PP_barycentre; auto.
RingPP.
unfold not in |- *; intros; apply H2.
replace k with (k + k' + - k').
rewrite H3.
ring.
ring.
replace (1 + - (k + k') + (k + k')) with 1.
auto with *.
ring.
ring.
Qed.
 
Lemma points_plan_espace :
 forall A B C D E : PO,
 ~ coplanaires A B C D ->
 (exists k : R,
    (exists k' : R,
       vec D E = add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C)))) \/
 (exists a : R,
    (exists b : R,
       (exists d : R,
          add_PP (cons d D) (cons (1 + - d) E) =
          add_PP (cons a A) (add_PP (cons b B) (cons (1 + - (a + b)) C))))).
intros A B C D E H0; try assumption.
assert (~ alignes A B C).
elim non_coplanaires_expl with (A := A) (B := B) (C := C) (D := D);
 [ intros H H1; try clear non_coplanaires_expl; try exact H | try trivial ].
elim repere_espace with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros a H1; elim H1; intros b H2; elim H2; intros c H3;
    try clear H2 H1 repere_espace; try exact H3
 | try trivial ].
elim (classic (a + b + c = 0)); intros.
left.
unfold vec in |- *.
rewrite H3; rewrite H4.
exists b; exists c.
replace a with (- (b + c)).
RingPP.
replace a with (a + b + c + - (b + c)).
rewrite H4; ring.
ring.
right.
exists (/ (a + b + c) * a).
exists (/ (a + b + c) * b).
exists (/ (a + b + c) * (a + b + c + -1)).
apply mult_PP_regulier with (a + b + c); auto.
replace
 (mult_PP (a + b + c)
    (add_PP (cons (/ (a + b + c) * (a + b + c + -1)) D)
       (cons (1 + - (/ (a + b + c) * (a + b + c + -1))) E))) with
 (add_PP (cons (a + b + c + -1) D) (cons 1 E)).
2: FieldPP (a + b + c).
rewrite H3.
FieldPP (a + b + c).
Qed.
 
Theorem position_relative_droite_plan :
 forall A B C D E : PO,
 D <> E ->
 ~ alignes A B C ->
 para_plan_dr (plan A B C) (droite D E) \/ perce (droite D E) (plan A B C).
unfold perce in |- *; intros.
elim (classic (coplanaires A B C D)); intros.
elim (classic (coplanaires A B C E)); intros.
left; try assumption.
apply paralleles_droite_incluse; auto.
apply droite_incluse_plan2; auto.
right; try assumption.
split; [ idtac | try assumption ].
red in |- *; intros; apply H2.
elim droite_incluse_plan with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ try clear droite_incluse_plan; auto | auto | auto | auto ].
apply def_contact with D; auto with geo.
lapply (points_plan_espace (A:=A) (B:=B) (C:=C) (D:=D) E); auto; intros.
elim H2;
 [ intros H3; elim H3;
    [ intros k H4; elim H4;
       [ intros k' H5; try clear H4 H3 H2; try exact H5 ] ]
 | intros H3; try clear H2 ].
left; try assumption.
apply vecteurs_para_plan_dr with (k := k) (k' := k'); auto.
right; try assumption.
elim H3; intros a H2; elim H2; intros b H4; elim H4; intros d H5;
 try clear H4 H2 H3; try exact H5.
split; [ idtac | try assumption ].
red in |- *; intros; apply H1.
elim droite_incluse_plan with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ try clear droite_incluse_plan; auto | auto | auto | auto ].
apply def_contact with (barycentre (cons d D) (cons (1 + - d) E)); auto.
apply barycentre_alignes; auto.
replace (d + (1 + - d)) with 1.
discrR.
ring.
unfold coplanaires, coplanaires1 in |- *.
right; try assumption.
pattern 1 at 1 in |- *.
replace 1 with (d + (1 + - d)).
rewrite <- add_PP_barycentre.
rewrite H5.
exists a; exists b; auto.
replace (d + (1 + - d)) with 1.
discrR.
ring.
ring.
Qed.