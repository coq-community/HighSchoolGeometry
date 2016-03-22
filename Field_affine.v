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


Require Export Rutile.
Require Export Ring Field.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter PO : Type.
Parameter PP : Type.
Parameter add_PP : PP -> PP -> PP.
Parameter mult_PP : R -> PP -> PP.
Parameter cons : R -> PO -> PP.
Parameter zero : PP.
(* AM anneau abstrait*)
Parameter AM : Type.
Parameters (plusAM multAM minusAM : AM -> AM -> AM).
Parameters (zeroAM : AM) (unAM : AM).
Parameter oppAM : AM -> AM.
 
Axiom AM_theory :
    ring_theory zeroAM unAM plusAM multAM minusAM oppAM (eq(A:=AM)).
(* Injections de R, PO et PP dans AM*)
Parameter fR : R -> AM.
Parameter fPO : PO -> AM.
Parameter fPP : PP -> AM.
 
Axiom fPP_inj : forall A B : PP, fPP A = fPP B -> A = B.
(* Transports des opérations *)
Axiom fRadd : forall x y : R, fR (x + y) = plusAM (fR x) (fR y).
Axiom fRmult : forall x y : R, fR (x * y) = multAM (fR x) (fR y).
Axiom fRopp : forall x : R, fR (- x) = oppAM (fR x).
Axiom fR0 : fR 0 = zeroAM.
Axiom fR1 : fR 1 = unAM.
Hypothesis
  fcons : forall (x : R) (A : PO), fPP (cons x A) = multAM (fR x) (fPO A).
Axiom
  fmult : forall (x : R) (A : PP), fPP (mult_PP x A) = multAM (fR x) (fPP A).
Axiom fadd : forall A B : PP, fPP (add_PP A B) = plusAM (fPP A) (fPP B).
Axiom fzeroPP : fPP zero = zeroAM.
(* Construction d'un corps *)
Parameter invAM : AM -> AM.
Definition divAM x y := multAM x (invAM y).
Axiom fRinv : forall x : R, x <> 0 -> fR (/ x) = invAM (fR x).
Axiom nonzeroAM : forall k : R, k <> 0 -> fR k <> zeroAM.
Axiom invAM_l : forall x : AM, x <> zeroAM -> multAM (invAM x) x = unAM.

Lemma AMField : field_theory
  zeroAM unAM plusAM multAM minusAM oppAM divAM invAM(eq(A:=AM)).
constructor.
 apply AM_theory.
 rewrite <- fR1 in |- *; apply nonzeroAM; discrR.
 reflexivity.
 exact invAM_l.
Qed.

Add Field AMfield : AMField.

(* Tactiques de simplification dans PP*)
 
Ltac RewriteAM :=
  repeat
   rewrite fcons ||
     rewrite fmult ||
       rewrite fadd ||
         rewrite fRopp ||
           rewrite fRadd ||
             rewrite fRmult ||
               rewrite fR0 ||
                 rewrite fzeroPP ||
                   (rewrite fRinv; [ idtac | auto ]) || rewrite fR1.
 
Ltac RingPP := apply fPP_inj; RewriteAM; (ring || ring_simplify).
 
Lemma l1 : forall A B C : PP, add_PP A B = C -> A = add_PP C (mult_PP (-1) B).
intros.
rewrite <- H.
RingPP.
Qed.
 
Lemma l2 : forall A B C : PP, add_PP A B = C -> B = add_PP C (mult_PP (-1) A).
intros.
rewrite <- H.
RingPP.
Qed.
 
Ltac RingPP1 H := rewrite (l1 H).
 
Ltac RingPP2 H := rewrite (l2 H).
 
Ltac FieldPP k :=
  apply fPP_inj; RewriteAM; field; generalize (nonzeroAM (k:=k)); RewriteAM;
   auto.
 
Lemma add_PP_zero : forall (P : PP) (A : PO), add_PP P (cons 0 A) = P.
intros; RingPP.
Qed.
 
Lemma add_PP_A :
 forall (a b : R) (A : PO), add_PP (cons a A) (cons b A) = cons (a + b) A.
intros; RingPP.
Qed.
 
Lemma add_PP_sym : forall P Q : PP, add_PP P Q = add_PP Q P.
intros; RingPP.
Qed.
 
Lemma add_PP_assoc :
 forall P Q T : PP, add_PP P (add_PP Q T) = add_PP (add_PP P Q) T.
intros; RingPP.
Qed.
 
Lemma def_mult_PP :
 forall (a k : R) (A : PO), mult_PP k (cons a A) = cons (k * a) A.
intros; RingPP.
Qed.
 
Lemma mult_PP_1 : forall (a : R) (A : PO), mult_PP 1 (cons a A) = cons a A.
intros; RingPP.
Qed.
 
Lemma mult_PP_0 : forall (a : R) (A : PO), mult_PP 0 (cons a A) = cons 0 A.
intros; RingPP.
Qed.
 
Lemma distrib_mult_PP :
 forall (k : R) (P Q : PP),
 add_PP (mult_PP k P) (mult_PP k Q) = mult_PP k (add_PP P Q).
intros; RingPP.
Qed.
 
Lemma distrib_mult_cons :
 forall (a b k : R) (A B : PO),
 add_PP (cons (k * a) A) (cons (k * b) B) =
 mult_PP k (add_PP (cons a A) (cons b B)).
intros; RingPP.
Qed.
 
Lemma mult_PP_regulier :
 forall (k : R) (P Q : PP), k <> 0 -> mult_PP k P = mult_PP k Q -> P = Q :>PP.
intros.
replace P with (mult_PP (/ k) (mult_PP k P)).
rewrite H0.
FieldPP k.
FieldPP k.
Qed.
 
Lemma add_PP_regulier :
 forall (P Q : PP) (a : R) (A : PO),
 add_PP P (cons a A) = add_PP Q (cons a A) :>PP -> P = Q :>PP.
intros P Q c C H; try assumption.
RingPP1 H.
RingPP.
Qed.
 
Lemma add_PP_reg_gauche :
 forall (P Q : PP) (a : R) (A : PO),
 add_PP (cons a A) P = add_PP (cons a A) Q :>PP -> P = Q :>PP.
intros P Q a A H; try assumption.
RingPP2 H.
RingPP.
Qed.
 
Lemma PP_0 : forall A B : PO, cons 0 A = cons 0 B.
intros; RingPP.
Qed.
 
Lemma zero_add_PP : forall (P : PP) (A : PO), add_PP (cons 0 A) P = P :>PP.
intros.
RingPP.
Qed.
 
Lemma def_zero : forall A : PO, zero = cons 0 A.
intros; RingPP.
Qed.
 
Lemma inversion_kPP :
 forall (k : R) (P Q : PP),
 k <> 0 -> P = mult_PP k Q -> Q = mult_PP (/ k) P :>PP.
intros.
rewrite H0.
FieldPP k.
Qed.
 
Lemma cons_comp :
 forall (a b : R) (A B : PO), a = b -> A = B -> cons a A = cons b B.
intros.
rewrite H; rewrite H0; auto.
Qed.
 
Axiom
  cons_inj :
    forall (a b : R) (A B : PO),
    cons a A = cons b B -> a <> 0 -> a = b /\ A = B.
