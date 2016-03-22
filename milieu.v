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


Require Export barycentre.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition milieu (A B : PO) := barycentre (cons 1 A) (cons 1 B).
Hint Unfold milieu: geo.
 
Lemma milieu_permute :
 forall A B I : PO, I = milieu A B :>PO -> I = milieu B A :>PO.
unfold milieu in |- *; intros.
rewrite permute_barycentre; auto.
discrR.
Qed.
 
Lemma add_PP_milieu :
 forall A B : PO, add_PP (cons 1 A) (cons 1 B) = cons 2 (milieu A B) :>PP.
unfold milieu in |- *; intros.
repeat rewrite <- add_PP_barycentre; auto.
discrR.
Qed.
 
Lemma milieu_trivial : forall A : PO, A = milieu A A :>PO.
intros.
apply conversion_PP with (a := 2) (b := 2); auto.
rewrite <- add_PP_milieu; RingPP.
discrR.
Qed.
 
Lemma prop_vecteur_milieu :
 forall B C A' O : PO,
 A' = milieu B C :>PO -> add_PP (vec O B) (vec O C) = mult_PP 2 (vec O A').
unfold milieu in |- *; intros.
generalize (prop_vecteur_bary (a:=1) (b:=1) (A:=B) (B:=C) (G:=A') O);
 intros H5.
rewrite <- (prop_vecteur_bary (a:=1) (b:=1) (A:=B) (B:=C) (G:=A') O); auto.
Ringvec.
discrR.
Qed.
 
Lemma alignes_milieu :
 forall A B I : PO, I = milieu A B :>PO -> alignes A B I.
unfold milieu in |- *; intros.
rewrite H.
apply barycentre_alignes.
discrR.
Qed.
 
Lemma add_PP_milieu_asso :
 forall A B C : PO,
 add_PP (cons 1 A) (cons 2 (milieu B C)) =
 add_PP (cons 2 (milieu A B)) (cons 1 C) :>PP.
intros A B C; try assumption.
repeat rewrite <- add_PP_milieu; try discrR; auto.
RingPP.
Qed.
 
Lemma vecteur_milieu :
 forall A B M : PO,
 vec A M = mult_PP (/ 2) (vec A B) :>PP -> M = milieu A B :>PO.
intros; unfold milieu in |- *.
rewrite (colineaire_barycentre (k:=/ 2) (A:=A) (B:=B) (C:=M)); auto.
cut (1 + - / 2 = / 2); intros; auto with real.
rewrite H0.
RReplace (/ 2) (/ 2 * 1).
apply homogene_barycentre; auto with real.
Qed.
 
Lemma milieu_vecteur2 :
 forall A B M : PO,
 M = milieu A B :>PO -> vec A M = mult_PP (/ 2) (vec A B) :>PP.
intros; unfold vec in |- *.
cut (2 <> 0); intros; auto with real.
apply mult_PP_regulier with 2; auto.
replace (mult_PP 2 (add_PP (cons (-1) A) (cons 1 M))) with
 (add_PP (cons (-2) A) (cons 2 M)).
rewrite H; rewrite <- add_PP_milieu.
FieldPP 2.
RingPP.
Qed.
 
Lemma milieu_vecteur :
 forall A B M : PO, M = milieu A B :>PO -> vec A M = vec M B.
intros.
rewrite H.
apply mult_PP_regulier with 2; auto with real.
VReplace (mult_PP 2 (vec A (milieu A B)))
 (add_PP (cons (-2) A) (cons 2 (milieu A B))).
VReplace (mult_PP 2 (vec (milieu A B) B))
 (mult_PP (-1) (add_PP (cons 2 (milieu A B)) (cons (-2) B))).
rewrite <- add_PP_milieu; RingPP.
Qed.
 
Lemma milieu_vecteur_double :
 forall A B M : PO, M = milieu A B :>PO -> vec A B = mult_PP 2 (vec A M) :>PP.
intros.
VReplace (vec A B) (add_PP (vec A M) (vec M B)).
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=M)); auto.
Ringvec.
Qed.
 
Lemma egalite_vecteur_milieu :
 forall A B M : PO, vec A M = vec M B -> M = milieu A B.
unfold milieu in |- *; intros.
apply def_vecteur_bary_rec; auto with real.
rewrite <- H; Ringvec.
Qed.
Hint Resolve milieu_vecteur milieu_vecteur_double milieu_vecteur2
  vecteur_milieu alignes_milieu milieu_trivial milieu_permute
  egalite_vecteur_milieu: geo.
 
Lemma triangle_milieu_distinct :
 forall A B C : PO, ~ alignes B C A -> A <> milieu B C :>PO.
intros.
contrapose H.
auto with geo.
Qed.
 
Lemma milieu_distinct : forall A B : PO, A <> B :>PO -> A <> milieu A B :>PO.
intros A B H; try assumption.
apply distinct_produit_vecteur with (B := B) (a := / 2); auto with real.
rewrite <- (milieu_vecteur2 (A:=A) (B:=B) (M:=milieu A B)); auto.
Qed.
 
Lemma milieu_distinct2 : forall A B : PO, A <> B :>PO -> B <> milieu A B :>PO.
intros A B H; try assumption.
apply distinct_produit_vecteur with (B := A) (a := / 2); auto with real.
cut (vec (milieu A B) B = mult_PP (/ 2) (vec A B)); intros.
VReplace (vec B (milieu A B)) (mult_PP (-1) (vec (milieu A B) B)).
rewrite H0.
cut (2 <> 0); intros; auto with real.
Fieldvec 2.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=milieu A B)); auto.
rewrite <- (milieu_vecteur2 (A:=A) (B:=B) (M:=milieu A B)); auto.
Qed.
Hint Resolve triangle_milieu_distinct milieu_distinct milieu_distinct2: geo.
 
Lemma existence_milieu :
 forall A B : PO, ex (fun I : PO => I = milieu A B :>PO).
intros.
exists (milieu A B); auto.
Qed.
Comments "soit_milieu" "pose" "I" "milieu" "de" "AB" "et" "echoue" "si" "A=B"
  "et" "ajoute" "des" "hypotheses".
 
Ltac soit_milieu A B I :=
  elim (existence_milieu A B); intros I; intros;
   lapply (milieu_distinct (A:=A) (B:=B)); try assumption;
   match goal with
   | h:(I = milieu A B) |- _ =>
       rewrite <- h; intros; lapply (milieu_distinct2 (A:=A) (B:=B));
        try assumption; rewrite <- h; intros
   end.
 
Lemma droite_milieu :
 forall A B C I J : PO,
 I = milieu A B -> J = milieu A C -> mult_PP 2 (vec I J) = vec B C.
intros.
rewrite H0; rewrite H.
VReplace (mult_PP 2 (vec (milieu A B) (milieu A C)))
 (add_PP (mult_PP (-1) (cons 2 (milieu A B))) (cons 2 (milieu A C))).
repeat rewrite <- add_PP_milieu.
Ringvec.
Qed.
 
Lemma deux_milieux_distincts :
 forall A B C I J : PO,
 A <> C :>PO -> I = milieu A B :>PO -> J = milieu B C :>PO -> I <> J :>PO.
intros.
lapply (droite_milieu (A:=B) (B:=A) (C:=C) (I:=I) (J:=J)); auto with geo;
 intros.
contrapose H.
apply vecteur_nul_conf.
rewrite <- H2; auto.
rewrite <- H3; Ringvec.
Qed.
 
Lemma triangle_triangle_milieux :
 forall A B C A' B' C' : PO,
 triangle A B C ->
 A' = milieu B C :>PO ->
 B' = milieu A C :>PO -> C' = milieu A B :>PO -> triangle A' B' C'.
intros.
deroule_triangle A B C.
red in |- *; intros; apply H3.
assert (A' <> B').
apply (deux_milieux_distincts (A:=B) (B:=C) (C:=A)); auto with geo.
halignes H7 ipattern:k.
apply colineaire_alignes with k; auto.
rewrite <- (droite_milieu (A:=B) (B:=A) (C:=C) (I:=C') (J:=A'));
 auto with geo.
rewrite <- (droite_milieu (A:=C) (B:=A) (C:=B) (I:=B') (J:=A'));
 auto with geo.
VReplace (vec C' A') (mult_PP (-1) (vec A' C')).
rewrite H9; Ringvec.
Qed.
 
Lemma add_PP_milieu_permute :
 forall A B C : PO,
 add_PP (cons 1 A) (cons 2 (milieu B C)) =
 add_PP (cons 2 (milieu A C)) (cons 1 B) :>PP.
intros A B C; try assumption.
repeat rewrite <- add_PP_milieu; auto.
Ringvec.
Qed.
 
Definition centre_gravite (A B C : PO) :=
  barycentre (cons 1 A) (cons 2 (milieu B C)).
 
Lemma centre_gravite_ordre_cycle :
 forall A B C : PO, centre_gravite A B C = centre_gravite B C A :>PO.
unfold centre_gravite in |- *; intros.
generalize (add_PP_milieu_permute A B C); intros.
apply conversion_PP with (a := 3) (b := 3); auto with *.
rewrite <- add_PP_barycentre; try discrR; auto with *.
rewrite <- add_PP_barycentre; try discrR; auto with *.
rewrite H.
rewrite (milieu_permute (A:=A) (B:=C) (I:=milieu A C)); auto.
Ringvec.
Qed.
 
Lemma centre_gravite_ordre_cycle2 :
 forall A B C : PO, centre_gravite A B C = centre_gravite C A B :>PO.
unfold centre_gravite in |- *; intros.
generalize (add_PP_milieu_asso A B C); intros.
apply conversion_PP with (a := 3) (b := 3); auto with *.
rewrite <- add_PP_barycentre; try discrR; auto with *.
rewrite <- add_PP_barycentre; try discrR; auto with *.
rewrite H.
RingPP.
Qed.
 
Lemma centre_gravite_ordre_permute :
 forall A B C : PO, centre_gravite A B C = centre_gravite A C B :>PO.
unfold centre_gravite in |- *; intros.
rewrite (milieu_permute (A:=C) (B:=B) (I:=milieu C B)); auto.
Qed.
Hint Resolve centre_gravite_ordre_permute centre_gravite_ordre_cycle2
  centre_gravite_ordre_cycle: geo.
 
Lemma triangle_medianes_triangle :
 forall A B C I J : PO,
 triangle A B C ->
 I = milieu B C :>PO -> J = milieu A B :>PO -> ~ alignes A I J.
intros.
deroule_triangle A B C.
red in |- *; intros; apply H2.
cut (A <> J); intros.
halignes H6 ipattern:k.
cut (k <> 0); intros.
apply colineaire_alignes with ((1 + - k) * / k).
replace (vec A C) with (mult_PP 2 (vec J I)).
replace (vec A B) with (mult_PP 2 (vec A J)).
VReplace (vec J I) (add_PP (vec A I) (mult_PP (-1) (vec A J))).
rewrite H8.
Fieldvec k.
rewrite (milieu_vecteur_double (A:=A) (B:=B) (M:=J)); auto with geo.
rewrite (droite_milieu (A:=B) (B:=A) (C:=C) (I:=J) (J:=I)); auto with geo.
apply distinct_col_nonzero with (2 := H8); auto.
rewrite H1; apply milieu_distinct; auto.
Qed.
 
Lemma centre_gravite_mediane_vecteur :
 forall A B C I G : PO,
 I = milieu B C :>PO ->
 G = centre_gravite A B C :>PO ->
 vec A G = mult_PP (/ 3) (mult_PP 2 (vec A I)) :>PP.
unfold centre_gravite in |- *; intros.
rewrite <- H in H0.
cut (3 <> 0); intros; auto with real.
apply mult_PP_regulier with 3; auto.
rewrite <- (prop_vecteur_bary (a:=1) (b:=2) (A:=A) (B:=I) (G:=G) A); auto.
Fieldvec 3.
Qed.