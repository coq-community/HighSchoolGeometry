Require Export triangles_semblables.
Require Export orientation.

(* Main proof of Ptolemy's theorem *)

Lemma EntreDeuxVec_sym :
forall (A B C M N :PO),
         vecEntreDeuxVec A B C M -> A<>N->
         cons_AV ( vec A B) (vec A M) = cons_AV (vec A N) (vec A C) ->
         vecEntreDeuxVec A B C N.
intros A B C M N H H0 H1.
unfold vecEntreDeuxVec in *.
assert (H2: A<>B /\ A<>C /\ A<>M).
elim H;intros [H3[H4 H5]];
    deroule_orient H3;deroule_orient H5;repeat split;auto.
destruct H2 as [H2 [H3 H4]].
assert (H5: cons_AV (vec A B)(vec A N) = cons_AV (vec A M) (vec A C)).
rewrite <-(@Chasles A B A M A N);auto.
rewrite H1.
rewrite plus_commutative.
rewrite ->(@Chasles A M A N A C);auto.
elim H;intros [H6[H7 H8]].
left.
split;auto.
split;auto.
apply (@anglesEgaux_orient A M C);auto.
apply (@anglesEgaux_orient A B M);auto.
right.
split;auto.
split;auto.
apply (@anglesEgaux_orient A M B);auto.
apply permute_angles;auto.
apply (@anglesEgaux_orient A C M);auto .
apply permute_angles;auto.
Qed.

Lemma EntreDeuxPoint :
forall ( A B M :PO),
          positifColineaire A B M -> positifColineaire B A M -> distance A B = distance A M + distance M B.
intros A B M H0 H1.
destruct H0 as [k [H2 [H3 H4]]].
destruct H1 as [k' [H5 [H6 H7]]].
assert (vec M B  = mult_PP k' (vec A B)).
rewrite (@opp_vecteur B A).
rewrite ->mult_mult_vec.
rewrite (@opp_vecteur B M).
rewrite H6.
rewrite ->mult_mult_vec.
replace (-1 * k') with (k' *-1);auto.
ring.
assert (H8: vec A B = add_PP (vec A M)(vec M B)).
symmetry.
apply (@Chasles_vec A M B) ;auto.
rewrite H3 in H8.
rewrite H in H8.
replace ( add_PP(mult_PP k(vec A B)) (mult_PP k' (vec A B)))
             with (mult_PP (k+k')(vec A B)) in H8;[idtac|RingPP].
assert (H9: add_PP (mult_PP (k+k') (vec A B)) (mult_PP (-1) (vec A B)) = zero).
rewrite <-H8.
rewrite <-opp_vecteur.
rewrite Chasles_vec.
unfold vec.
rewrite add_PP_A.
replace (-1+1) with 0.
rewrite<-def_zero;auto.
ring.
replace ( add_PP(mult_PP (k+k') (vec A B)) (mult_PP (-1) (vec A B)))
             with (mult_PP (k+k'+-1)(vec A B)) in H9;[idtac|RingPP].
elim (@produit_vecteur_nul (k+k'+-1) A B H9);intros H10.
assert ( H11 : distance A M = Rabs k *distance A B)
  by (apply (@colinearite_distance k A B A M H3)) .
assert ( H12 : distance M B = Rabs k' *distance A B)
  by (apply (@colinearite_distance k' A B M B H)) .
rewrite Rabs_right in H11;[idtac|lra].
rewrite Rabs_right in H12;[idtac|lra].
rewrite H11.
rewrite H12.
rewrite<-Rmult_plus_distr_r.
assert (k+k' =1).
auto with *.
rewrite H0; ring.
elim H2;auto.
Qed.

Require Export Droite_espace.


Lemma Exists_Intersection1 : (* on peut prouver grace au lemme
droites_non_paralleles *)
forall (A B C D :PO),
          vecEntreDeuxVec A B C D ->
          exists E :PO, alignes A D E /\ alignes B C E.
intros A B C D H.
assert (H0 : ~alignes A D B /\ A <>D)
 by(destruct H as [[_ [H2 _]]|[_ [_ H2]]];deroule_orient H2;auto with geo).
destruct H0 as [H0 H1].
assert (H2 : ~alignes A D C)
 by(destruct H as [[_ [_ H3 ]]|[_ [H3 _]]];deroule_orient H3;auto with geo).
assert (H3 : B<>C)
 by(destruct H as [[H4 [_ _]]|[H4 [_ _]]];deroule_orient H4;auto with geo).
destruct (@existence_pt_intersection A D B C ) as [E H4];auto.
assert (H4: ~ paralleles (droite A D) (droite B C)).
red;intros H4.
destruct (@existence_representant_vecteur A B C) as [D' H5].
destruct (@paralleles_vecteur A D B C ) as [k H6];auto.
destruct H as [[H7 [H8 H9]]|[H7 [H8 H9]]].
assert (aire(vec B C)(vec A D) = 0) by (apply aire_colinearite with (k:=k) ;auto).
rewrite <-(@Chasles_vec B A C) in H.
rewrite aire_distrib_r in H.
assert (aire (vec B A)(vec A D) <0).
VReplace (vec B A) (mult_PP (-1) (vec A B)).
rewrite aire_colineaire_l.
unfold orient in H8;lra.
assert (aire (vec A C)(vec A D) <0).
rewrite aire_anti_symetrique.
unfold orient in H9;lra.
lra.
assert (aire(vec B C)(vec A D) = 0) by (apply aire_colinearite with (k:=k) ;auto).
rewrite <-(@Chasles_vec B A C) in H.
rewrite aire_distrib_r in H.
assert (aire (vec B A)(vec A D) >0).
VReplace (vec B A) (mult_PP (-1) (vec A B)).
rewrite aire_colineaire_l.
rewrite aire_anti_symetrique.
unfold orient in H9.
replace (-1) with (-(1)) by ring.
rewrite Ropp_mult_distr_l_reverse.
rewrite Ropp_mult_distr_r_reverse.
lra.
assert (aire (vec A C)(vec A D) >0).
unfold orient in H8;auto.
lra.
elim (@droites_non_paralleles  B C A D H3 H1 H4);auto.
intros H5.
(*here we use an axiom of plane geometry,
which one to say that every 4 points are COPLANAR   *)
assert (H6: coplanaires B C A D) by apply geometrie_plane.
elim H5;auto.
exists E;auto.
apply def_pt_intersection2;auto.
Qed.


Lemma  angles_representants_unitaires_r :
(*consequence de l'axiom angles_representants_unitaires *)
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    cons_AV (vec A B) (vec C D) =
    cons_AV  (vec A B)
      (representant_unitaire (vec C D)).
intros A B C D E F H H0.
assert (H1: cons_AV (vec A B)(vec C D) =
    cons_AV (representant_unitaire (vec A B))(representant_unitaire(vec C D))).
apply angles_representants_unitaires ;auto.
rewrite H1.
destruct (@existence_representant_unitaire A B H) as [B' H2].
assert (H3 : exists k:R, k>0 /\
                                      vec A B = mult_PP k (vec A B')).
apply (@egalite_representant_unitaire A B' B);auto.
destruct (@def_representant_unitaire2 A B B' H H2) as  [_ [H3 _]].
apply unitaire_distincts ;auto.
rewrite H2;apply representant_unitaire_bis;auto.
destruct H3 as [k[H3 H4]].
rewrite <-H2.
destruct (@existence_representant_unitaire C D H0) as [D' H5].
rewrite <-H5.
rewrite H4.
symmetry.
apply  angle_produit_positif_l;auto.
destruct (@def_representant_unitaire2 A B B' H H2) as  [_ [H6 _]].
apply unitaire_distincts ;auto.
destruct (@def_representant_unitaire2 C D D' H0 H5) as  [_ [H6 _]].
apply unitaire_distincts ;auto.
Qed.

Lemma  angles_representants_unitaires2 :
(*consequence de l'axiom angles_representants_unitaires *)
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    cons_AV (vec A B) (vec C D) =
    cons_AV (representant_unitaire (vec A B)) (vec C D).
intros A B C D E F H H0.
assert (H1: cons_AV (vec A B)(vec C D) =
    cons_AV (representant_unitaire (vec A B))(representant_unitaire(vec C D))).
apply angles_representants_unitaires ;auto.
rewrite H1.
destruct (@existence_representant_unitaire C D H0) as [D' H2].
assert (H3 : exists k:R, k>0 /\
                                      vec C D = mult_PP k (vec C D')).
apply (@egalite_representant_unitaire C D' D);auto.
destruct (@def_representant_unitaire2 C D D' H0 H2) as  [_ [H3 _]].
apply unitaire_distincts ;auto.
rewrite H2;apply representant_unitaire_bis;auto.
destruct H3 as [k[H3 H4]].
rewrite <-H2.
destruct (@existence_representant_unitaire A B H) as [B' H5].
rewrite <-H5.
rewrite H4.
symmetry.
apply  angle_produit_positif_r2;auto.
destruct (@def_representant_unitaire2 C D D' H0 H2) as  [_ [H6 _]].
apply unitaire_distincts ;auto.
destruct (@def_representant_unitaire2 A B B' H H5) as  [_ [H6 _]].
apply unitaire_distincts ;auto.
Qed.


Lemma Exists_Intersection :
forall (A B C D :PO),
          vecEntreDeuxVec A B C D ->
          exists E :PO, cons_AV ( vec A B) (vec A E) = cons_AV (vec A D) (vec A C)
                               /\  positifColineaire B C E /\ positifColineaire C B E.
intros A B C D H.
assert (H1: A<>B /\ A<>C /\ A<>D).
elim H;intros [H2[H3 H4]];
    deroule_orient H2;deroule_orient H4;repeat split;auto.
destruct H1 as [H1 [H2 H3]].
destruct (@existence_representant_unitaire A B) as [B' H4];auto.
destruct(@existence_representant_cons (cons_AV (vec A D)(vec A C)) A B' A) as [E' [H5 H6]].
unfold distance.
destruct (@def_representant_unitaire2 A B B' H1 H4) as [_ [H7 _]].
rewrite H7.
rewrite sqrt_1;auto.
assert (H7: A<>E').
red;intros.
rewrite H0 in H5.
assert (distance E' E' =0) by (apply distance_refl2;auto).
rewrite H7 in H5.
(*info auto with real.*)
assert (1<>0) by lra.
elim H8;auto.
assert (H8 : cons_AV (vec A B)(vec A E') = cons_AV (vec A B') (vec A E')).
rewrite H4.
apply angles_representants_unitaires2;auto.
rewrite <-H8 in H6.
assert (H9 :cons_AV (vec A E')(vec A C) = cons_AV (vec A B)(vec A D)).
rewrite <-(@Chasles A B A E' A D);auto.
rewrite <-H6.
rewrite plus_commutative.
rewrite ->(@Chasles A E' A D A C);auto.
assert (H10:vecEntreDeuxVec A B C E').
apply (@EntreDeuxVec_sym A B C D E');auto.
destruct (@Exists_Intersection1 A B C E') as [E [H11 H12]];auto.
exists E.
destruct (@vecEntreDeuxVec_intersection_middle A B C E'  H10 E ) as [H13 [H14 H15]];auto.
repeat split;auto.
destruct H15 as [k [H16[H17 H18]]].
rewrite (@angle_produit_positif_r k A E' E A B);auto.
Qed.

Ltac deroule_sont_cocycliques :=
  match goal with H : sont_cocycliques ?A ?B ?C ?D|- _ =>
  generalize H ; let name := fresh in intros name  ;
  unfold sont_cocycliques in name;
  destruct name ;decompose [and] name; clear name;
 repeat match goal with H' : circonscrit ?O ?A ?B ?C  |- _ =>
  unfold circonscrit  in H';
  decompose [and] H' ; clear H' end ;
 repeat match goal with H' : isocele ?O ?A ?B  |- _ =>
  unfold isocele  in H'
  end
end.

Lemma sont_cocycliques_avec_ordre_cycle:
forall (A B C D :PO),
         sont_cocycliques A B C D ->sont_cocycliques B C D A.
intros A B C D H.
deroule_sont_cocycliques .
unfold sont_cocycliques .
exists x.
unfold circonscrit in *.
unfold isocele in *.
repeat split ;auto.
rewrite H4 in H2;auto.
rewrite H3 in H0;auto.
rewrite H4 in H2;auto.
Qed.

Lemma sont_cocycliques_avec_ordre_permute:
forall (A B C D :PO),
         sont_cocycliques A B C D ->sont_cocycliques A B D C.
intros A B C D H.
deroule_sont_cocycliques .
unfold sont_cocycliques .
exists x.
unfold circonscrit in *.
unfold isocele in *.
repeat split ;auto.
Qed.


Theorem Ptolemee:
forall (A B C D : PO),
         orient A B C -> orient A B D -> orient C D A -> orient C D B ->
         sont_cocycliques A B C D ->
         (distance A B  * distance C D ) + (distance B C *distance D A) =
              distance A C  * distance B D .
intros A B C D H0 H1 H2 H3 H4.
assert ( H5: A<>B /\ A<>C /\ ~alignes A B C).
deroule_orient H0;repeat split;auto.
destruct H5 as [H5 [H6 H7]].
assert ( H8: A<>B /\ A<>D /\ ~alignes A B D).
deroule_orient H1;repeat split;auto.
destruct H8 as [H8 [H9 H10]].
assert ( H11: C<>D /\ C<>A /\ ~alignes C D A).
deroule_orient H2;repeat split;auto.
destruct H11 as [H11 [H12 H13]].
assert ( H14: C<>D /\ C<>B /\ ~alignes C D B).
deroule_orient H3;repeat split;auto.
destruct H14 as [H14 [H15 H16]].
destruct (@Exists_Intersection C D B A) as [E [H17 [H18 H19]]].
unfold vecEntreDeuxVec.
left.
split;auto.
split;auto.
apply orient_cycle;apply orient_cycle;auto.
assert (H20 : E<>C).
red;intro.
rewrite H in H18.
destruct H18 as [k [_ [H20 _]]].
assert (alignes D B C) by (apply (@colineaire_alignes k);auto).
assert (alignes C D B) by (apply alignes_ordre_cycle2 ;auto).
elim H16;auto.
assert (H21 : cons_AV (vec C E) (vec C B) = cons_AV (vec C D) (vec C A)).
rewrite <-(@Chasles C E C A C B);auto.
rewrite <-H17.
rewrite (plus_commutative).
rewrite Chasles ;auto.

assert (H40 : E<>D).
red;intros.
rewrite H in H17.
rewrite <-angle_nul in H17; auto.
destruct (@angle_nul_positif_colineaire C A B ) as [k [H41 H42]];auto.
assert (alignes C A B ) by (apply (@colineaire_alignes k);auto).
assert (alignes A B C) by (apply alignes_ordre_cycle ;auto).
elim H7;auto.
assert (H41 : E<>B).
red;intros.
rewrite H in H21.
rewrite <-angle_nul in H21; auto.
destruct (@angle_nul_positif_colineaire C D A ) as [k [H41 H42]];auto.
assert (alignes C D A ) by (apply (@colineaire_alignes k);auto).
elim H13;auto.


assert (H22 : cons_AV (vec D E) (vec D C) = cons_AV (vec A B )(vec A C)).
destruct H18 as [k [H22 [H23 H24]]].
rewrite H23.
rewrite (@angle_produit_positif_l k D B D C);auto.
apply consAD_orient_consAV;auto.
apply cocyclicite;auto with geo.
apply sont_cocycliques_avec_ordre_cycle;auto.
apply orient_cycle;auto.


assert (H23:cons_AV (vec A C) (vec A D) = cons_AV (vec B C )(vec B E)).
destruct H19 as [k [H23 [H24 H25]]].
rewrite H24.
rewrite (@angle_produit_positif_r2 k B D B C);auto.
apply consAD_orient_consAV;auto.
apply cocyclicite;auto with geo.
apply sont_cocycliques_avec_ordre_cycle.
apply sont_cocycliques_avec_ordre_cycle;auto.
apply orient_cycle;apply orient_cycle;auto.
apply orient_cycle;apply orient_cycle;auto.


assert ( H24 : trianglesSD E C D  B C A ).
unfold trianglesSD.
repeat split  ;auto with geo.
unfold triangle.
red;intros.
destruct H18 as [k [_ [H24 H25]]].
assert (alignes D B E) by (apply (@colineaire_alignes k);auto).
assert (alignes E D B) by (apply alignes_ordre_cycle2;auto).
assert (alignes E D C) by (apply alignes_ordre_permute;auto).
assert (alignes D B C) by (apply alignes_trans2 with (A :=E);auto).
assert (alignes C D B) by (apply alignes_ordre_cycle2;auto).
elim H16;auto.

assert ( H25 : trianglesSD E B C D A C ).
unfold trianglesSD.
repeat split  ;auto with geo.
unfold triangle.
red;intros.
destruct H19 as [k [_ [H25 H26]]].
assert (alignes B D E) by (apply (@colineaire_alignes k);auto).
assert (alignes E B D) by (apply alignes_ordre_cycle2;auto).
assert (alignes B C D) by (apply alignes_trans2 with (A :=E);auto).
assert (alignes C D B) by (apply alignes_ordre_cycle;auto).
elim H16;auto.

destruct (@trianglesSD_proportion E C D B C A H24)
 as [k [H26 [H27 [H28 H29]]]].
assert (H30: distance E D * distance C A =distance B A * distance C D).
rewrite H26.
rewrite H28.
ring.
rewrite (@distance_sym C A) in H30.
rewrite (@distance_sym B A) in H30.
destruct (@trianglesSD_proportion E B C D A C H25)
 as [k' [H31 [H32 [H33 H34]]]].
assert (H35: distance E B * distance A C =distance B C * distance D A).
rewrite H32.
rewrite H31.
ring.
rewrite (@distance_sym E B) in H35.
assert (H36 : distance B D = distance B E + distance E D) by
  (apply (@EntreDeuxPoint B D E H19 H18)).
rewrite H36.
rewrite <-H30.
rewrite <-H35.
ring.
Qed.
