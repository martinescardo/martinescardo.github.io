(*
Copyright (c) 2014, Vincent Siles, All rights reserved.

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3.0 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library.
*)

(*
This module started as an exercise to translate Martin Escardo's Agda proof
of omniscient of N\inf into Coq (the link provided at 
http://permalink.gmane.org/gmane.comp.lang.agda/3123
is unfortunately broken now)
.
The translation is quite litteral, with lots of assertions. I should tidy it a
bit someday.

Sorry for the unreadable names of lemmas ;)

V.
*)

Definition N2 := nat -> bool.

(* -- Definition (Natural order of binary numbers) *)
Definition le_bool (a b: bool) := a = true -> b = true. 

Definition ge_bool (a b : bool) := le_bool b a. 

(* -- Definition (Minimum of binary numbers). *)
Definition min (a b: bool) : bool := 
 match a with
   | false => false
   | true => b
 end.

Lemma min_ab_le_a: forall a b, le_bool (min a b) a. 
Proof.
now destruct a; destruct b; intuition.
Qed.

(* -- Definition (Extensional equality on the Cantor space). *)
Definition EqCantor (a b : N2) := forall i, a i = b i.

Definition Inf : N2 := fun _ => true.

(* -- Definition (Extensional ₂-valued functions on the Cantor space). *)
Definition extensional (P: N2 -> bool) := forall (a b : N2), EqCantor a b -> P a = P b.

Lemma extensionality : forall (X Y:Type) (f: X -> Y) (x y: X), x = y -> f x = f y.
Proof.
now intros; subst.
Qed.

Definition Ninf (P: N2) := forall i, ge_bool (P i) (P (S i)).

Fixpoint underline (n:nat) : N2 := 
  match n with
    | O => fun _ => false
    | S p => fun q => match q with 
                         | 0 => true
                         | S r => underline p r
                     end
  end.


Lemma underline0: forall n, underline n n = false.
Proof.
now induction n as [ | n hi]; intuition.
Qed.

Lemma underline1: forall n, underline (S n) n = true.
Proof.
now induction n as [ | n hi]; intuition.
Qed.

Lemma x0_eq_false_impl_x_eqCantor_underline0: forall (x: N2), Ninf x -> x 0  = false -> EqCantor x (underline 0).
Proof.
intros x hinf base n.
induction n as [ | n hi].
- now rewrite base; simpl.
- simpl in *.
  unfold Ninf in hinf.
  specialize hinf with n.
  unfold ge_bool, le_bool in hinf.
  destruct (x n).
  discriminate.
  destruct (x (S n)).
  symmetry; now apply hinf.
  reflexivity.
Qed. 

Definition prd (k : N2) : N2 := fun n => k (S n).

Lemma Ninf_closed_under_prd: forall (x: N2), Ninf x -> Ninf (prd x).
Proof.
intros x hinf n.
unfold ge_bool, prd, le_bool; intros h.
now apply hinf.
Qed.

Lemma xn_eq_true_impl_xSn_eq_false_impl_x_eq_underlineSn:
  forall (x: N2), Ninf x -> forall n, x n = true -> x (S n) = false -> EqCantor x (underline (S n)).
Proof.
intros x hx n; revert x hx.
induction n as [ | n hi]; intros x m r s i.
  assert (by_cases: EqCantor x (underline 1)).
  intros [ | p].
  - simpl in *; assumption.
  - assert (by_nested_induction: forall i, x (S i) = false).
    induction i0 as [ | i0 hi].
    + assumption.
    + unfold Ninf in m; specialize m with (S i0).
      unfold ge_bool, le_bool in m.
      destruct (x (S (S i0))).
      * now rewrite m in hi.
      * reflexivity.
    + now apply by_nested_induction.
  - now apply by_cases.

  - destruct i as [ | i].
    + assert (by_nested_induction : forall n, x n = true -> x 0 = true).
      induction n0 as [ | n0 h1].
      * tauto.
      * unfold Ninf in m; specialize m with n0.
        unfold ge_bool, le_bool in m.
        now intuition.
      * now apply (by_nested_induction (S n)).
     + apply (hi (prd x)).
       now apply Ninf_closed_under_prd.
       now intuition.
       now intuition.
Qed.

Lemma Ninf_underline_N_le_Inf: forall (x: N2), Ninf x-> (forall n, ~ EqCantor x(underline n)) -> 
  EqCantor x Inf.
Proof.
intros x m f.
assert (lemma: forall n, x n = true).
  induction n as [ | n hi].
    assert (claim: x 0 <> false).
      intros r; apply (f 0).
      now apply x0_eq_false_impl_x_eqCantor_underline0.
    now destruct (x 0); intuition.
    assert (claim: x (S n) <> false).
      intros r; apply (f (S n)).
      now apply xn_eq_true_impl_xSn_eq_false_impl_x_eq_underlineSn.
    now destruct (x (S n)); intuition.
now intros r; apply lemma.
Qed.

Lemma density: forall (P: N2 -> bool), extensional P -> (forall n, P (underline n) = true) ->
  P Inf = true -> forall (x: N2), Ninf x -> P x = true.
Proof.
intros p hext f r x m.
assert (claim: forall n, p x = false -> ~ EqCantor x (underline n)).
  intros n hp hc.
  apply hext in hc.
  rewrite (f n) in hc; rewrite hp in hc; discriminate.

assert(claim': p x = false -> forall n, ~EqCantor x (underline n)).
  now intros hp n; apply claim.

assert (claimInf: p x = false -> ~EqCantor x Inf).
  intros hp hc; apply hext in hc.
  rewrite hp in hc; rewrite r in hc; discriminate hc.

assert (lemma: p x <> false).
  intro t.
  apply claimInf.
  assumption.
  now apply (Ninf_underline_N_le_Inf x m (claim' t)).

now destruct (p x); intuition.
Qed.

Fixpoint x (P: N2 -> bool) (n:nat) { struct n } : bool :=
  match n with
    | O => P (underline 0)
    | S n => min (x P n) (P (underline(S n)))
  end.

Theorem T3_6 : forall P: N2 -> bool, extensional P -> {x: N2 & Ninf x /\ 
    (P x = true -> forall y: N2, Ninf y -> P y = true) }.
Proof. 
intros P hext .

assert (lemma0: Ninf (x P)).
  now intros b; apply min_ab_le_a.

assert (dagger0: forall n, EqCantor (x P) (underline n) -> P (underline n) = false).
  destruct n as [ | n].
    intros r.
    now apply (r 0).

    intros r.
    assert (s : x P n = true).
      transitivity (underline (S n) n).
      now apply (r n).
      now apply underline1.

    assert (t : x P (S n) = false).
      transitivity (underline (S n) (S n)).
      now apply (r (S n)).
      now apply underline0.

    assert (u: P (underline (S n)) = x P (S n)).
      now simpl; rewrite s; simpl.

    now rewrite u.

assert (dagger1: EqCantor (x P) Inf -> forall n, P (underline n) = true).
  intros r [ | n ].
  now apply (r 0).

  assert (s: x P n = true) by (apply r).
  assert (t: x P (S n) = true) by apply r.
  assert (u: P (underline (S n)) = x P (S n)).
    now simpl; rewrite s; simpl.

  now rewrite u.

assert (claim0: P (x P) = true -> forall n, ~(EqCantor (x P) (underline n))).
  intros r n s.
  assert (lemma : EqCantor (x P ) (underline n) -> P (x P) = false).
  apply hext in s.
  rewrite s.
  now apply dagger0.

  rewrite r in lemma.
  now discriminate (lemma s).

assert (claim1 : P (x P) = true -> EqCantor (x P) Inf).
  intros r.
  now apply (Ninf_underline_N_le_Inf (x P) lemma0 (claim0 r)).

assert (claim2: P (x P) = true -> forall n, P (underline n) = true).
  intros r.
  now apply (dagger1 (claim1 r)).

assert (claim3: P (x P) = true -> P Inf = true).
  assert (fact: forall a b, a = true -> a = b -> b = true) by (intros; subst; intuition).
  intro r.
  apply (fact _ _ r).
  apply hext.
  now apply (claim1 r).

assert (lemma1: P (x P) = true -> forall (y: N2), Ninf y -> P y = true).
  intro r.
  apply (density P).
  assumption.
  now apply claim2.
  now apply claim3.

now exists (x P); intuition.
Qed.

Lemma two_equality_cases : forall (A: Type) (b: bool), (b = false -> A) -> (b = true -> A) -> A. 
Proof.
intros A b hfalse htrue.
now destruct b; intuition.
Qed.

Theorem Ninf_is_omniscient: forall (p: N2 -> bool), extensional p -> 
   {x: N2 & Ninf x /\ p x = false}+{forall x: N2, Ninf x -> p x = true}.
Proof.
intros p hext.
assert (e: {x : N2 & Ninf x /\ (p x = true -> forall y: N2, Ninf y -> p y = true)}).
  now apply T3_6.

destruct e as [x [m hx2]].

assert (case0: p x = false -> {x0 : N2 & Ninf x0 /\ p x0 = false}+{forall x0: N2, Ninf x0 -> p x0 = true }).
  intros r; left.
  now exists x; split.

assert (case1: p x = true -> {x0 : N2 & Ninf x0 /\ p x0 = false}+{forall x0: N2, Ninf x0 -> p x0 = true }).
  intros r; right.
  intros y hy; now apply hx2.

now apply (two_equality_cases _ (p x)).
Qed.

Print Assumptions Ninf_is_omniscient.
