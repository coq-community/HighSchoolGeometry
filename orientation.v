Require Export aire_signee.
Require Export angles_droites.
Require Export angles_vecteurs.
Require Export Droite_espace.
Require Export triangles_semblables.
Definition orient ( A B C :PO) : Prop :=
     aire (vec A B) (vec A C) >0.

Lemma orient_cycle :
    forall (A B C :PO), orient A B C -> orient B C A.
intros A B C H.
unfold orient in *.
rewrite aire_ordre_cycle ;auto.
Qed.


Lemma orient_compensation :
    forall (A B C :PO), ~orient A B C \/ ~orient B A C .
intros A B C.
elim (classic (orient A B C));(intros H;auto).
assert (H0 : orient B C A ) by (apply orient_cycle ;auto).
right;red;intros H1.
unfold orient in *.
rewrite aire_anti_symetrique in H1.
lra.
Qed.

Lemma position_3points_1:
   forall (A B C :PO), (~ orient A B C /\ ~ orient B A C) \/ ~ alignes A B C.
intros A B C.
elim (classic (~ orient A B C /\ ~ orient B A C));(intros H;auto).
right.
elim (@not_and_or (~orient A B C)(~orient B A C));auto;intro H1.
assert(orient A B C) by (apply NNPP;auto).
red;intros H2.
unfold orient in H0.
assert ( aire (vec A B)(vec A C) = 0) by apply (@aire_alignement A B C H2) .
lra.

assert(orient B A C) by (apply NNPP;auto).
red;intros H2.
assert (alignes B A C);auto with geo.
unfold orient in H0.
assert ( aire (vec B A)(vec B C) = 0) by apply (@aire_alignement B A C H3) .
lra.
Qed.

Lemma position_3points_2:
   forall (A B C :PO), orient A B C \/ orient B A C \/ alignes A B C.
intros A B C .
destruct (@total_order_T (aire (vec A B)(vec A C)) 0) as [[H | H ] |H].
right;left.
apply orient_cycle;apply orient_cycle.
unfold orient.
rewrite aire_anti_symetrique;lra.
elim (classic (A=B));intros H0.
right;right.
rewrite H0;auto with geo.
destruct (@aire_nulle_colineaires A B A C H0 H) as [k H1].
right;right.
apply  colineaire_alignes with (k:=k);auto.
left.
unfold orient;auto.
Qed.
Lemma orient_4point:
(*correspondant un axiom de Knuth
  prouve grace a l'axiom position_4points *)
forall (A B C D : PO), orient A B D -> orient B C D ->
          orient C A D -> orient A B C.
intros A B C D H0 H1 H2.
unfold orient in *.
rewrite aire_ordre_cycle2 in H2.
assert (H4:aire (vec A D) (vec B A) >0).
rewrite aire_anti_symetrique.
VReplace (vec B A) (mult_PP (-1) (vec A B)).
rewrite aire_colineaire_l;lra.
assert (H5: aire (vec A D) (vec B C) >0).
rewrite <-(@Chasles_vec B A C).
rewrite aire_distrib_l;lra.
assert (H6 : aire (vec D B)(vec B C)>0).
rewrite aire_anti_symetrique.
VReplace (vec D B) (mult_PP (-1) (vec B D)).
rewrite aire_colineaire_r;lra.
assert (H7: aire (vec A B) (vec B C) >0).
rewrite <-(@Chasles_vec A D B).
rewrite aire_distrib_r;lra.
rewrite <-(@Chasles_vec A B C ).
rewrite aire_distrib_l.
rewrite aire_ABAB;lra.
Qed.

Lemma orient_deroule :
    forall ( A B C :PO), orient A B C ->
             ~orient B A C /\ ~alignes A B C /\
             A<>B /\ A <> C /\ B<>C.
intros A B C H.
cut (~orient B A C);intro H0.
cut (~alignes A B C);intro H1.
repeat split;auto.
red;intro H2.
rewrite H2 in H.
assert (alignes B B C ) by intuition.
rewrite H2 in H1.
elim H1;assumption.
red;intro H2.
rewrite H2 in H.
assert (alignes C B C ) by intuition.
rewrite H2 in H1.
elim H1;assumption.
red;intro H2.
rewrite H2 in H1.
assert (alignes A C C ) by intuition.
elim H1;assumption.
destruct (position_3points_1 A B C) as [[H2 H3]|h4] ;intuition.
elim (orient_compensation A B C );intros H1;elim H1;auto.
Qed.


Ltac deroule_orient H:=
(*find out others trivial hypotheses from the one*)
(*  match goal with H : orient ?A ?B ?C|- _ =>*)
  generalize H; let name := fresh in intros name ; decompose [and] (@orient_deroule _ _ _ name ).
(*end.*)

Definition  positifColineaire ( A B M:PO):Prop :=
       exists k :R, A <> B /\ vec A M = mult_PP k (vec A B) /\ k>0.

Definition  negatifColineaire ( A B M:PO):Prop :=
       exists k :R, A <> B /\ vec A M = mult_PP k (vec A B) /\ k<0.

Axiom colineaire_position :
      forall A B C :PO, A<>B->
              C = A \/ positifColineaire A B C \/ negatifColineaire A B C.
Axiom positifColineaire_permute :
      forall A B C :PO, positifColineaire A B C -> positifColineaire A C B.
Axiom positifColineaire_negatifColineaire :
       forall A B C :PO, positifColineaire A B C ->
                B=C \/ negatifColineaire C B A \/ negatifColineaire B C A  .
Axiom positifColineaire_negatifColineaire1 :
       forall A B C :PO, positifColineaire A B C ->
                positifColineaire B A C -> negatifColineaire C B A  .

Axiom negatifColineaire_permute :
      forall A B C :PO, negatifColineaire A B C -> negatifColineaire A C B.
Axiom negatifColineaire_positifColineaire :
       forall A B C :PO, negatifColineaire A B C ->
                positifColineaire C A B /\ positifColineaire B A C.

Lemma inversion_colineaire :
 forall (k : R) (A B C : PO),
 A <> C -> vec A C = mult_PP k (vec A B) -> vec A B = mult_PP (/ k) (vec A C).
intros.
cut (k <> 0); intros.
rewrite H0.
Fieldvec k.
contrapose H.
apply vecteur_nul_conf.
rewrite H0; rewrite H1; Ringvec.
Qed.

Lemma alignes_positifColineaire :
           forall ( A B M :PO), A<>B ->alignes A B M ->
                    positifColineaire A B M \/ positifColineaire B A M.
intros A B M H H0.
elim H0;intros H1.
elim H;auto.
assert (H2: col_vec A B A M) by (apply alignes1_colineaire;auto).
elim H2;intros k H3.
elim (Rle_or_lt k 0);intro H4.

assert ( H5 : vec B M =mult_PP (1-k) (vec B A)).
rewrite <-(Chasles_vec B A M) .
rewrite ->(opp_vecteur A B) .
rewrite H3.
rewrite (mult_mult_vec A B (1-k) (-1)).
replace ((1-k)* -1) with (k-1); [idtac | ring].
assert (H6: add_PP (mult_PP (-1) (vec A B))(mult_PP k (vec A B))=
                   mult_PP (-1 +k) (vec A B )) by RingPP.
rewrite H6.
replace (-1 + k ) with (k-1);[auto|ring].
assert (H7: 1-k >0).
lra.
right;unfold positifColineaire.
exists (1-k);auto.
left;unfold positifColineaire.
exists k;auto.
Qed.


(* BEGIN consequences *)
Lemma positifColineaire_orient_l:
forall (A B C M :PO), orient A B C -> positifColineaire A B M ->
          orient A M C.
intros A B C M H [k [H0 [H1 H2]]].
unfold orient in *.
rewrite H1.
rewrite aire_colineaire_l.
apply Rmult_gt_0_compat;auto.
Qed.

Lemma negatifColineaire_orient_l:
forall (A B C M :PO), orient A B C -> negatifColineaire A B M ->
          orient A C M.
intros A B C M H [k [H0 [H1 H2]]].
unfold orient in *.
rewrite H1.
rewrite aire_colineaire_r.
rewrite aire_anti_symetrique.
rewrite  Ropp_mult_distr_r_reverse.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_gt_0_compat;auto with real.
Qed.

Lemma positifColineaire_orient_r:
forall (A B C M :PO), orient A B C -> positifColineaire A C M ->
          orient A B M.
intros A B C M H [k [H0 [H1 H2]]].
unfold orient in *.
rewrite H1.
rewrite aire_colineaire_r.
apply Rmult_gt_0_compat;auto.
Qed.

Lemma negatifColineaire_orient_r:
forall (A B C M :PO), orient A B C -> negatifColineaire A C M ->
          orient A M B.
intros A B C M H [k [H0 [H1 H2]]].
unfold orient in *.
rewrite H1.
rewrite aire_colineaire_l.
rewrite aire_anti_symetrique.
rewrite  Ropp_mult_distr_r_reverse.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_gt_0_compat;auto with real.
Qed.


Lemma positifColineaire_orient_inv_l:
forall (A B C M :PO), orient A B C -> orient A M C ->
          alignes A B M -> positifColineaire A B M.
intros A B C M H H0 H1 .
destruct H1 as [H2|H3].
deroule_orient H.
elim H4;auto.
assert (H2: col_vec A B A M) by (apply alignes1_colineaire;auto).
destruct H2 as [k H4].
destruct (@total_order_T k 0) as [[H1 | H1] |H1].
assert(orient A C M).
apply negatifColineaire_orient_l with (B:=B);auto.
exists k; deroule_orient H;auto.
destruct (orient_compensation C M A);elim H5;apply orient_cycle;auto.
assert ( A = M) by (apply (@produit_zero_conf k A M A B);auto).
deroule_orient H0.
elim H7;auto.
unfold positifColineaire.
exists k;repeat split;auto.
deroule_orient H;auto.
Qed.

Lemma positifColineaire_orient_inv_r:
forall (A B C M :PO), orient A B C -> orient A B M  ->
           alignes A C M ->  positifColineaire A C M.
intros A B C M H H0 H1 .
destruct H1 as [H2|H3].
deroule_orient H.
elim H6;auto.
assert (H2: col_vec A C A M) by (apply alignes1_colineaire;auto).
destruct H2 as [k H4].
destruct (@total_order_T k 0) as [[H1 | H1] |H1].
assert(orient A M B).
apply negatifColineaire_orient_r with (C:=C) ;auto.
exists k;deroule_orient H;auto.
destruct (orient_compensation B M A);elim H5;apply orient_cycle;auto.
assert ( A = M) by (apply (@produit_zero_conf k A M A C);auto).
deroule_orient H0.
elim H9;auto.
unfold positifColineaire.
exists k;repeat split;auto.
deroule_orient H;auto.
Qed.


Lemma negatifColineaire_orient_inv_l:
forall (A B C M :PO), orient A B C -> orient A C M->alignes A B M->
          negatifColineaire A B M.
intros A B C M H H0 H1.
destruct H1 as [H2|H2].
deroule_orient H.
elim H4;auto.
destruct (@alignes1_colineaire A B M) as [k H3];auto.
destruct (@Rtotal_order k 0) as [H4 |[H4|H4]].
exists k;deroule_orient H;auto.
rewrite H4 in H3.
assert ( A =M) by (apply (@produit_zero_conf 0 A M A B);auto).
deroule_orient H0.
elim H9;auto.
assert (H5 : orient A M C).
apply (@positifColineaire_orient_l A B C M ); auto.
exists k;deroule_orient H;auto.
elim (@orient_compensation A M C);intros H6;elim H6;
   [auto |apply orient_cycle;apply orient_cycle;auto].
Qed.

Lemma negatifColineaire_orient_inv_r:
forall (A B C M :PO), orient A B C -> orient A M B->alignes A C M->
          negatifColineaire A C M.
intros A B C M H H0 H1.
destruct H1 as [H2|H2].
deroule_orient H.
elim H6;auto.
destruct (@alignes1_colineaire A C M) as [k H3];auto.
destruct (@Rtotal_order k 0) as [H4 |[H4|H4]].
exists k;deroule_orient H;auto.
rewrite H4 in H3.
assert ( A =M) by (apply (@produit_zero_conf 0 A M A C);auto).
deroule_orient H0.
elim H7;auto.
assert (H5 : orient A B M ).
apply (@positifColineaire_orient_r A B C M ); auto.
exists k;deroule_orient H; auto.
elim (@orient_compensation A B M );intros H6;elim H6;
   [auto |apply orient_cycle;apply orient_cycle;auto].
Qed.




(* Lemma for angle and orientation *)
Lemma orient_SinusPositif :
forall A B C  :PO,
           orient A B C-> Sin (cons_AV (vec A B )(vec A C ))>0.
intros A B C H.
generalize H;intros H0.
unfold orient in H0.
rewrite def_aire in *;deroule_orient H;auto.
elim (@distance_pos A B );intros H10 ;
      [idtac|elim (@distincts_dist_non_nulle A B H3);auto].
elim (@distance_pos A C );intros H11 ;
      [idtac|elim (@distincts_dist_non_nulle A C H5);auto].
assert (H9 :0< distance A C * Sin(cons_AV (vec A B )(vec A C)) ).
apply Rmult_lt_reg_l with (r:= distance A B);auto with real.
replace (distance A B *0)  with 0  ;auto with real.
red.
apply Rmult_lt_reg_l with (r:= distance A C);auto with real.
replace (distance A C *0)  with 0  ;auto with real.
Qed.

Lemma anglesEgaux_orient :
forall (A B C M N P : PO), orient A B C -> M<>N -> M <>P->
         cons_AV (vec M N) (vec M P) = cons_AV (vec A B ) ( vec A C)->
         orient M N P.
intros A B C M N P H H0 H1 H2.
generalize H;intros H3.
unfold orient in H3.
unfold orient .
rewrite def_aire in *;deroule_orient H;auto.
elim (@distance_pos A B );intros H11 ;
      [idtac|elim (@distincts_dist_non_nulle A B H6);auto].
elim (@distance_pos A C );intros H12 ;
      [idtac|elim (@distincts_dist_non_nulle A C H8);auto].
elim (@distance_pos M N );intros H13 ;
      [idtac|elim (@distincts_dist_non_nulle M N H0);auto].
elim (@distance_pos M P );intros H14 ;
      [idtac|elim (@distincts_dist_non_nulle M P H1);auto].
rewrite H2.
apply Rmult_gt_0_compat;auto.
apply Rmult_gt_0_compat;auto.
replace 0 with (distance A B *0) in H3;auto with real.
apply orient_SinusPositif;auto.
Qed.

Lemma  consAD_orient_consAV:
forall A B C M N P :PO,
double_AV (cons_AV (vec A B)(vec A C))= double_AV (cons_AV (vec M N) (vec M P))->
orient A B C -> orient M N P ->
cons_AV (vec A B) (vec A C) = cons_AV (vec M N) (vec M P).
intros A B C M N P H H0 H1.
unfold double_AV in H.
deroule_orient H0.
deroule_orient H1.
destruct  (tout_angle_a_une_mesure (A:=A) (B:=B) (C:=A) (D:=C)) as [x H15]; auto with geo.
destruct  (tout_angle_a_une_mesure (A:=M) (B:=N) (C:=M) (D:=P)) as [y H16]; auto with geo.
rewrite <-H15 in *.
rewrite <-H16 in *.
rewrite <-add_mes_compatible in H.
rewrite <-add_mes_compatible in H.
replace (x+x) with (2*x) in H.
replace (y+y) with (2*y) in H.
cut (sin x = sin y).
intros H17.
cut (cos x = cos y).
intros H18.
apply egalite_angle_trigo;auto.
assert (H19:sin (2*x) = sin (2*y)) by (apply sin_deux_mes;auto).
repeat rewrite duplication_sin in H19.
rewrite H17 in H19.
apply Rmult_eq_reg_l with (r:=sin y).
apply Rmult_eq_reg_l with (r:=2);auto with real.
apply Rgt_not_eq.
rewrite (@egalite_sin_Sin M N P y);auto.
apply orient_SinusPositif;auto.
assert (H19:cos (2*x) = cos (2*y)) by (apply cos_deux_mes;auto).
repeat rewrite duplication_cos2 in H19.
apply Rsqr_inj.
assert (sin x >0) by
(rewrite (@egalite_sin_Sin A B C x);auto; apply orient_SinusPositif;auto).
lra.
assert (sin y >0) by
(rewrite (@egalite_sin_Sin M N P y);auto; apply orient_SinusPositif;auto).
lra.
apply Rmult_eq_reg_l with (r:=2);auto with real.
assert (-(2*Rsqr (sin x)) = -((2*Rsqr (sin y)))) by (apply Rplus_eq_reg_l with (r:=1);auto with real).
replace (2 * Rsqr(sin x)) with (-(-(2 * Rsqr(sin x))));auto with real.
replace (2 * Rsqr(sin y)) with (-(-(2 * Rsqr(sin y))));auto with real.
ring.
ring.
Qed.

Lemma  consAD_orient_consAVplusPi:
forall A B C M N P :PO,
double_AV (cons_AV (vec A B)(vec A C))= double_AV (cons_AV (vec M N) (vec M P))->
orient A B C -> orient M P N ->
cons_AV (vec A B) (vec A C) = plus (cons_AV (vec M N) (vec M P)) (image_angle pi).
intros A B C M N P H H0 H1.
unfold double_AV in H.
deroule_orient H0.
deroule_orient H1.
destruct  (tout_angle_a_une_mesure (A:=A) (B:=B) (C:=A) (D:=C)) as [x H15]; auto with geo.
destruct  (tout_angle_a_une_mesure (A:=M) (B:=N) (C:=M) (D:=P)) as [y H16]; auto with geo.
rewrite <-H15 in *.
rewrite <-H16 in *.
rewrite <-add_mes_compatible in H.
rewrite <-add_mes_compatible in H.
replace (x+x) with (2*x) in H; [idtac|ring].
replace (y+y) with (2*y) in H; [idtac|ring].
cut (sin x = -sin y).
intros H17.
cut (cos x = -cos y).
intros H18.
rewrite <-add_mes_compatible.
apply egalite_angle_PiPres_trigo;auto.
assert (H19:sin (2*x) = sin (2*y)) by (apply sin_deux_mes;auto).
repeat rewrite duplication_sin in H19.
rewrite H17 in H19.
replace (cos x) with ( - -cos x);auto with real.
apply Ropp_eq_compat.
apply Rmult_eq_reg_l with (r:=sin y).
apply Rmult_eq_reg_l with (r:=2);auto with real.
rewrite <-H19.
rewrite Ropp_mult_distr_l_reverse.
rewrite Ropp_mult_distr_r_reverse;auto.

assert (Sin (cons_AV(vec M P)(vec M N)) >0) by (apply orient_SinusPositif;auto).
assert (cons_AV (vec M P) (vec M N) = opp (cons_AV (vec M N) (vec M P))).
apply opp_angle.
rewrite Chasles;auto.
rewrite <-angle_nul;auto.
rewrite <-H16 in H18.
rewrite <-mes_opp in H18.
rewrite <-(@egalite_sin_Sin M P N (-y)) in H13;auto.
rewrite  sin_impaire in H13.
assert (sin y <0).
lra.
apply Rlt_not_eq;auto.

assert (H19:cos (2*x) = cos (2*y)) by (apply cos_deux_mes;auto).
repeat rewrite duplication_cos2 in H19.
rewrite (@Rsqr_neg (sin y)) in H19.
apply Rsqr_inj.
assert (sin x >0) by
(rewrite (@egalite_sin_Sin A B C x);auto; apply orient_SinusPositif;auto).
lra.

assert (Sin (cons_AV(vec M P)(vec M N)) >0) by (apply orient_SinusPositif;auto).
assert (cons_AV (vec M P) (vec M N) = opp (cons_AV (vec M N) (vec M P))).
apply opp_angle.
rewrite Chasles;auto.
rewrite <-angle_nul;auto.
rewrite <-H16 in H17.
rewrite <-mes_opp in H17.
rewrite <-(@egalite_sin_Sin M P N (-y)) in H13;auto.
rewrite  sin_impaire in H13.
lra.
apply Rmult_eq_reg_l with (r:=2);auto with real.
assert (-(2*Rsqr (sin x)) = -((2*Rsqr (-sin y)))) by (apply Rplus_eq_reg_l with (r:=1);auto with real).
replace (2 * Rsqr(sin x)) with (-(-(2 * Rsqr(sin x))));auto with real.
replace (2 * Rsqr(-sin y)) with (-(-(2 * Rsqr(-sin y))));auto with real.
Qed.




(*  Des consequences concernant l'intersection*)
Definition vecEntreDeuxVec ( A B C M :PO) : Prop :=
           (orient A B C /\ orient A B M /\ orient A M C)\/
           (orient A C B /\ orient A C M /\ orient A M B).

Lemma (*lemme*) vecEntreDeuxVec_permute :
forall ( A B C M :PO), vecEntreDeuxVec A B C M ->
          vecEntreDeuxVec A C B M.
intros A B C M [[H0 [H1 H2]]|[H0 [H1 H2]]].
right;auto.
left;auto.
Qed.

Lemma vecEntreDeuxVec_intersection_middle1:
           forall ( A B C D :PO),orient A B C -> vecEntreDeuxVec A B C D ->
           forall M:PO, alignes A D M /\ alignes B C M ->
           positifColineaire A D M.
intros A B C D H H0 M [H2 H1] .
elim H0;intros [H3 [H4 H5]].
destruct H2 as [H2|H2].
deroule_orient H5;elim H8;auto.
destruct (@alignes1_colineaire A D M) as [k H6];auto.
destruct (@Rtotal_order k 0) as [H7|[H7|H7]].
assert (orient A C M)
  by (apply (@negatifColineaire_orient_l A D C M H5 );auto;
  exists k; deroule_orient H5;auto).
assert (orient A M B)
  by (apply (@negatifColineaire_orient_r A B D M H4 );auto;
  exists k; deroule_orient H4;auto).
assert (orient M B C).
apply orient_4point with (D:=A);auto.
apply orient_cycle; auto.
apply orient_cycle;auto.
apply orient_cycle;auto.
deroule_orient H10.
elim H14;apply alignes_ordre_cycle2;auto.
assert (A=M) by (apply produit_zero_conf with (k:=k) (C:=A)(D:=D);auto).
rewrite <-H8 in H1.
deroule_orient H3.
elim H12;auto with geo.
exists k;repeat split;auto.
deroule_orient H5;auto.
destruct  (@orient_compensation A B C) as [H6|H6].
elim H6;auto.
elim H6;apply orient_cycle;apply orient_cycle;auto.
Qed.


Lemma vecEntreDeuxVec_intersection_middle2:
           forall ( A B C D  :PO),orient A B C -> vecEntreDeuxVec A B C D ->
           forall M:PO, alignes A D M /\ alignes B C M ->
           positifColineaire B C M /\ positifColineaire C B M.
intros A B C D  H H0 M [H2 H1].
elim H0;intros [H3 [H4 H5]].
assert (positifColineaire A D M) by  (apply(@vecEntreDeuxVec_intersection_middle1 A B C D );auto).
assert (orient A B M) by (apply positifColineaire_orient_r with (C:=D);auto).
assert (orient A M C) by (apply  positifColineaire_orient_l with (B:=D);auto).
split.
apply (@positifColineaire_orient_inv_l B C A M);auto.
apply orient_cycle;assumption.
apply orient_cycle;assumption.
apply (@positifColineaire_orient_inv_r C A B M);auto.
apply orient_cycle;apply orient_cycle;assumption.
apply orient_cycle;apply orient_cycle;assumption.
apply permute_alignes;assumption.
destruct  (@orient_compensation A B C) as [H6|H6].
elim H6;auto.
elim H6;apply orient_cycle;apply orient_cycle;auto.
Qed.

Lemma vecEntreDeuxVec_intersection_middle:
           forall ( A B C D :PO), vecEntreDeuxVec A B C D ->
           forall M:PO, alignes A D M /\ alignes B C M ->
           positifColineaire B C M /\ positifColineaire C B M /\ positifColineaire A D M.
intros A B C D H M [H1 H0].
elim H;intros [H2 [H3 H4]].
assert (positifColineaire B C M /\ positifColineaire C B M).
apply (@vecEntreDeuxVec_intersection_middle2 A B C D );auto.
assert (positifColineaire A D M).
apply (@vecEntreDeuxVec_intersection_middle1 A B C D );auto.
destruct H5 as [H7 H8].
split;auto.
assert (vecEntreDeuxVec A C B D) by
        (unfold vecEntreDeuxVec;left;split;auto).
assert (positifColineaire C B M /\ positifColineaire B C M).
apply (@vecEntreDeuxVec_intersection_middle2 A C B D );auto with geo.
assert (positifColineaire A D M).
apply (@vecEntreDeuxVec_intersection_middle1 A C B D );auto with geo.
destruct H6 as [H8 H9].
split;auto.
Qed.

Lemma vecEntreDeuxVec_intersection_left1:
           forall ( A B C D :PO), vecEntreDeuxVec A B C D ->
           forall M :PO, alignes A B M /\ alignes C D M ->
           (positifColineaire C D M -> positifColineaire A B M) /\
           (positifColineaire A B M -> positifColineaire C D M /\ positifColineaire M D C ) .
intros A B C D H M [H3 H2].
repeat split.
intro H1.
destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient A M C).
apply orient_cycle.
apply positifColineaire_orient_r with (C:=D);auto.
apply orient_cycle;apply orient_cycle;auto.
apply positifColineaire_orient_inv_l with (C:=C);auto.
assert (H4 : orient A C M).
apply orient_cycle;apply orient_cycle.
apply positifColineaire_orient_l with (B:=D);auto.
apply orient_cycle;auto.
apply positifColineaire_orient_inv_r with (B:=C);auto.

destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient C A M ).
apply orient_cycle;apply orient_cycle;auto.
apply positifColineaire_orient_l with (B:=B);auto.
apply positifColineaire_orient_inv_r with (B:=A);auto.
apply orient_cycle;apply orient_cycle;auto.
assert (H4 : orient C M A ).
apply orient_cycle;auto.
apply positifColineaire_orient_r with (C:=B);auto.
apply positifColineaire_orient_inv_l with (C:=A);auto.
apply orient_cycle;auto.



destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient M C A ).
apply orient_cycle.
apply positifColineaire_orient_l with (B:=B);auto.
assert (H5 : orient M D A ).
apply orient_cycle.
apply positifColineaire_orient_l with (B:=B);auto.
apply positifColineaire_orient_inv_l with (C:=A);auto with geo.
assert (H4 : orient M A C ).
apply orient_cycle;apply orient_cycle.
apply positifColineaire_orient_r with (C:=B);auto.
assert (H5 : orient M A D ).
apply orient_cycle;apply orient_cycle.
apply positifColineaire_orient_r with (C:=B);auto.
apply positifColineaire_orient_inv_r with (B:=A);auto with geo.
Qed.

Lemma vecEntreDeuxVec_intersection_left2:
           forall ( A B C D :PO), vecEntreDeuxVec A B C D ->
           forall M :PO, alignes A B M /\ alignes C D M ->
           (negatifColineaire C D M -> negatifColineaire A B M) /\
           (negatifColineaire A B M -> negatifColineaire C D M  ) .
intros A B C D H M [H3 H2].
repeat split;intro H1.
destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient A C M).
apply orient_cycle;apply orient_cycle.
apply negatifColineaire_orient_r with (C:=D);auto.
apply orient_cycle;apply orient_cycle;auto.
apply negatifColineaire_orient_inv_l with (C:=C);auto.
assert (H4 : orient A M C ).
apply orient_cycle.
apply negatifColineaire_orient_l with (B:=D);auto.
apply orient_cycle;auto.
apply negatifColineaire_orient_inv_r with (B:=C);auto.

destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient C M A ).
apply orient_cycle.
apply negatifColineaire_orient_l with (B:=B);auto.
apply negatifColineaire_orient_inv_r with (B:=A);auto.
apply orient_cycle;apply orient_cycle;auto.
assert (H4 : orient C A M  ).
apply orient_cycle;apply orient_cycle.
apply negatifColineaire_orient_r with (C:=B);auto.
apply negatifColineaire_orient_inv_l with (C:=A);auto.
apply orient_cycle;auto.
Qed.


Lemma vecEntreDeuxVec_intersection_right1:
           forall ( A B C D :PO), vecEntreDeuxVec A B C D ->
           forall M :PO, alignes A C M /\ alignes B D M ->
           (positifColineaire B D M -> positifColineaire A C M) /\
           (positifColineaire A C M -> positifColineaire B D M /\ positifColineaire M D B ) .
intros A B C  D H M [H3 H2].
repeat split.
intro H1.
destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient A B M).
apply orient_cycle;apply orient_cycle.
apply positifColineaire_orient_l with (B:=D);auto.
apply orient_cycle;auto.
apply positifColineaire_orient_inv_r with (B:=B);auto.
assert (H4 : orient A M B).
apply orient_cycle.
apply positifColineaire_orient_r with (C:=D);auto.
apply orient_cycle;apply orient_cycle;auto.
apply positifColineaire_orient_inv_l with (C:=B);auto.

destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient B M A ).
apply orient_cycle;auto.
apply positifColineaire_orient_r with (C:=C);auto.
apply positifColineaire_orient_inv_l with (C:=A);auto.
apply orient_cycle;auto.
assert (H4 : orient B A M ).
apply orient_cycle;apply orient_cycle;auto.
apply positifColineaire_orient_l with (B:=C);auto.
apply positifColineaire_orient_inv_r with (B:=A);auto.
apply orient_cycle;apply orient_cycle;auto.



destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient M A B ).
apply orient_cycle;apply orient_cycle.
apply positifColineaire_orient_r with (C:=C);auto.
assert (H5 : orient M A D ).
apply orient_cycle;apply orient_cycle.
apply positifColineaire_orient_r with (C:=C);auto.
apply positifColineaire_orient_inv_r with (B:=A);auto with geo.
assert (H4 : orient M B A ).
apply orient_cycle.
apply positifColineaire_orient_l with (B:=C);auto.
assert (H5 : orient M D A ).
apply orient_cycle.
apply positifColineaire_orient_l with (B:=C);auto.
apply positifColineaire_orient_inv_l with (C:=A);auto with geo.
Qed.

Lemma vecEntreDeuxVec_intersection_right2:
           forall ( A B C D :PO), vecEntreDeuxVec A B C D ->
           forall M :PO, alignes A C M /\ alignes B D M ->
           (negatifColineaire B D M -> negatifColineaire A C M) /\
           (negatifColineaire A C M -> negatifColineaire B D M  ) .
intros A B C D H M [H3 H2].
repeat split;intro H1.
destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient A M B ).
apply orient_cycle.
apply negatifColineaire_orient_l with (B:=D);auto.
apply orient_cycle;auto.
apply negatifColineaire_orient_inv_r with (B:=B);auto.
assert (H4 : orient A B M ).
apply orient_cycle;apply orient_cycle.
apply negatifColineaire_orient_r with (C:=D);auto.
apply orient_cycle;apply orient_cycle;auto.
apply negatifColineaire_orient_inv_l with (C:=B);auto.

destruct H as [[H19 [H20 H21]] |[H19 [H20 H21]]].
assert (H4 : orient B A M  ).
apply orient_cycle;apply orient_cycle.
apply negatifColineaire_orient_r with (C:=C);auto.
apply negatifColineaire_orient_inv_l with (C:=A);auto.
apply orient_cycle;auto.
assert (H4 : orient B M A ).
apply orient_cycle.
apply negatifColineaire_orient_l with (B:=C);auto.
apply negatifColineaire_orient_inv_r with (B:=A);auto.
apply orient_cycle;apply orient_cycle;auto.
Qed.



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

Lemma Exists_Intersection: (* on peut prouver grace au lemme
droites_non_paralleles *)
forall (A B C D :PO),
          vecEntreDeuxVec A B C D ->
          exists M :PO,positifColineaire B C M /\ positifColineaire C B M /\ positifColineaire A D M.
intros A B C D H.
destruct (@Exists_Intersection1 A B C D) as [M [H0 H1]];auto.
exists M.
apply vecEntreDeuxVec_intersection_middle;auto.
Qed.

(*Consequence concernant angles inscrits oriente*)
Axiom differencePiNull : image_angle 0 <>image_angle pi.

Require Export cocyclicite.

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






Theorem SommeAnglesInscritsOriente:
forall (A B C D : PO),
         sont_cocycliques A B C D ->orient A B C ->
                    orient A C D -> orient A B D.
intros A B C D H H0 H1.
destruct (@position_3points_2 A B D) as [H2|[H2|H2]];auto.
assert (H3:orient B C D).
apply orient_4point with (D:=A);auto.
apply orient_cycle;auto.
apply orient_cycle;auto.
apply orient_cycle;apply orient_cycle;auto.


assert (H4:cons_AV(vec A D )(vec A B) = cons_AV (vec C D)(vec C B)).
apply consAD_orient_consAV.
apply cocyclicite;auto with geo.
deroule_orient H2 ;auto with geo.
deroule_orient H3 ;auto with geo.
apply sont_cocycliques_avec_ordre_cycle.
apply sont_cocycliques_avec_ordre_permute.
apply sont_cocycliques_avec_ordre_cycle;apply sont_cocycliques_avec_ordre_cycle;auto.
apply orient_cycle;auto.
apply orient_cycle;auto.
assert (H5:cons_AV(vec A B )(vec A C) = cons_AV (vec D B)(vec D C)).
apply consAD_orient_consAV;auto.
apply cocyclicite;auto with geo.
deroule_orient H0 ;auto with geo.
deroule_orient H3 ;auto with geo.
apply sont_cocycliques_avec_ordre_permute.
apply sont_cocycliques_avec_ordre_cycle;auto.
apply orient_cycle;apply orient_cycle;auto.
assert (H6:cons_AV(vec A C )(vec A D) = cons_AV (vec B C)(vec B D)).
apply consAD_orient_consAV;auto.
apply cocyclicite;auto with geo.
deroule_orient H1 ;auto with geo.
deroule_orient H3 ;auto with geo.
apply sont_cocycliques_avec_ordre_cycle.
apply sont_cocycliques_avec_ordre_cycle;auto.
assert (plus (cons_AV (vec C D) (vec C B))
   (plus (cons_AV (vec D B) (vec D C)) (cons_AV (vec B C) (vec B D))) = image_angle pi).
apply somme_triangle;deroule_orient H3;auto.
rewrite <-H4 in H7.
rewrite <-H5 in H7.
rewrite <-H6 in H7.
rewrite Chasles in H7;(deroule_orient H0;deroule_orient H1;auto).
rewrite Chasles in H7;(deroule_orient H0;deroule_orient H1;auto).
rewrite <-angle_nul in H7;auto.

elim differencePiNull;auto.

assert (H3: col_vec A B A D) .
apply alignes1_colineaire;auto with geo.
unfold alignes in H2.
elim H2;intros;auto.
deroule_orient H0.
elim H6;auto.
destruct H3 as [k H4].
destruct (@total_order_T k 0) as [[H5| H5] |H5].
assert (H6: vec B D = mult_PP (1-k) (vec B A)).
rewrite <-(@Chasles_vec B A D) .
rewrite H4.
VReplace (vec A B) (mult_PP (-1) (vec B A)).
rewrite mult_mult_vec.
replace (k*-1) with (-k);[idtac|ring].
replace (1-k) with (1+(-k));auto with real.
VReplace (vec B A) (mult_PP (1) (vec B A)).
RingPP.
assert (H7: 1-k >0).
lra.
assert(H8 : orient D B C).
apply orient_cycle;apply orient_cycle.
apply positifColineaire_orient_r with (C:=A).
apply orient_cycle;auto.
exists (1-k);deroule_orient H0;auto.
assert (H9:cons_AV(vec D B )(vec D C) = cons_AV (vec A B)(vec A C)).
apply consAD_orient_consAV;auto.
apply cocyclicite;auto with geo.
deroule_orient H8 ;auto with geo.
deroule_orient H0 ;auto with geo.
apply sont_cocycliques_avec_ordre_cycle;auto.

assert (trianglesSD C A B C D B ).
repeat split.
deroule_orient H0;auto with geo.
deroule_orient H8;auto with geo.
auto.
rewrite (@angle_produit_positif_r (1-k) B A D  B C ) ;auto.
deroule_orient H0;auto with geo.
deroule_orient H0;auto with geo.
assert (cons_AV (vec C A)(vec C B) =cons_AV (vec C D)(vec C B)).
apply (@trianglesSD_angles_egaux  C A B C D B);auto.
assert (cons_AV (vec C A) (vec C D) = image_angle 0).
rewrite <-(@Chasles C A C B C D);(deroule_orient H0;deroule_orient H1;auto with geo).
rewrite H10.
rewrite Chasles;auto with geo.
rewrite (@ angle_nul C D) ;auto.
destruct (@angle_nul_positif_colineaire C A D) as [k' [H12 H13]];(deroule_orient H0;deroule_orient H1;auto).
assert (alignes C A D) .
apply colineaire_alignes with (k:=k');auto.
elim H23.
apply   alignes_ordre_permute .
apply alignes_ordre_cycle;auto.




assert (A=D).
apply (@produit_zero_conf k A D A B);auto.
deroule_orient H1.
elim H10;auto.

assert (orient A D C).
apply (@positifColineaire_orient_l A B C D H0);auto.
exists k;deroule_orient H0;auto.
elim (@orient_compensation D C A);intro.
elim H6.
apply orient_cycle;auto.

elim H6.
apply orient_cycle;auto.
Qed.
