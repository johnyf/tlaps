------------------------- MODULE NaturalsInduction -------------------------
(***************************************************************************)
(* This module contains useful theorems for inductive proofs and recursive *)
(* definitions over the naturals.                                          *)
(*                                                                         *)
(* Most of the statements of the theorems are decomposed in terms of       *)
(* definitions.  This is done for two reasons:                             *)
(*                                                                         *)
(*  - It makes it easier for the backends to instantiate the theorems      *)
(*    when those definitions are not expanded.                             *)
(*                                                                         *)
(*  - It can be convenient when writing proofs to use those definitions    *)
(*    rather than having to write out their expansions.                    *)
(***************************************************************************)
EXTENDS Integers, TLAPS

(***************************************************************************)
(* The following is the simple statement of inductions over the naturals.  *)
(* For predicates P defined by a moderately complex operator, it is often  *)
(* useful to hide the operator definition before using this theorem. That  *)
(* is, you first define a suitable operator P (not necessarily by that     *)
(* name), prove the two hypotheses of the theorem, and then hide the       *) 
(* definition of P when using the theorem.                                 *)
(***************************************************************************)
THEOREM NatInduction == 
          ASSUME NEW P(_),
                 P(0),
                 \A n \in Nat : P(n) => P(n+1)
          PROVE  \A n \in Nat : P(n)
OBVIOUS (*{ by (isabelle "(intro natInduct, auto)") }*)

THEOREM GeneralNatInduction ==
          ASSUME NEW P(_),
                 \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
          PROVE  \A n \in Nat : P(n)
<1> DEFINE Q(n) == \A m \in 0..n : P(m)
<1>1. Q(0) BY SMT
<1>2. \A n \in Nat : Q(n) => Q(n+1)  BY SMT
<1>3. \A n \in Nat : Q(n)  BY <1>1, <1>2, NatInduction
<1>4. QED BY ONLY <1>3, SMT

(***************************************************************************)
(* To prove something about a recursively defined function f, you must     *)
(* first prove that it equals its definition.  The following theorem       *)
(* FiniteNatInductiveDef allows you to do that for recursively defined     *)
(* functions with domain 0..n for an integer n.  I don't know how useful   *)
(* that will be in practice, but it's needed as a lemma in proving the     *)
(* corresponding theorem about recursively defined functions with domain   *)
(* Nat.                                                                    *)
(***************************************************************************)
FiniteNatInductiveDefConclusion(f, f0, Def(_,_), n) ==
     f = [i \in 0..n |-> IF i = 0 THEN f0 ELSE Def(f[i-1], i)]
FiniteNatInductiveDefHypothesis(f, f0, Def(_,_), n) == 
   (f =  CHOOSE g : g = [i \in 0..n |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)])
                                       
THEOREM FiniteNatInductiveDef ==
          ASSUME NEW Def(_,_)
          PROVE  \A n \in Nat:
                   \A f, f0 :
                     FiniteNatInductiveDefHypothesis(f, f0, Def, n)
                     => FiniteNatInductiveDefConclusion(f, f0, Def, n)
<1> USE DEF FiniteNatInductiveDefHypothesis, FiniteNatInductiveDefConclusion
<1> DEFINE P(n) == \A f, f0 :
                     FiniteNatInductiveDefHypothesis(f, f0, Def, n)
                      => FiniteNatInductiveDefConclusion(f, f0, Def, n)
<1>1. P(0)
  <2> SUFFICES ASSUME NEW f, NEW f0,
                      P(0)!(f, f0)!1
               PROVE  P(0)!(f, f0)!2
    OBVIOUS
  <2> DEFINE g == [i \in 0..0 |-> f0]
  <2> g = [i \in 0..0 |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)]
    BY SMT
  <2> QED
    OBVIOUS

<1>2. ASSUME NEW n \in Nat, P(n)
      PROVE  P(n+1)
  <2>1. SUFFICES ASSUME NEW f, NEW f0,
                        P(n+1)!(f, f0)!1
                 PROVE  P(n+1)!(f, f0)!2
   BY <1>2
  <2> DEFINE h == CHOOSE g : g = [i \in 0..n |-> IF i = 0 THEN f0 
                                                          ELSE Def(g[i-1], i)]
  <2>2. h = [i \in 0..n |-> IF i = 0 THEN f0 ELSE Def(h[i-1], i)]
    BY <1>2, <2>1, Auto
  <2> DEFINE g == [i \in 0..(n+1) |-> IF i \in 0..n THEN h[i]
                                                    ELSE Def(h[i-1], i)]
  <2>3. g = [i \in 0..(n+1) |-> IF i = 0 THEN f0
                                         ELSE Def(g[i-1], i)]
    <3>. HIDE DEF h
    <3>1. SUFFICES ASSUME NEW i \in 0 .. n+1
                   PROVE  g[i] = IF i = 0 THEN f0 ELSE Def(g[i-1], i)
      OBVIOUS
    <3>2. CASE i = 0
      BY <2>2, <3>2, SMT
    <3>3. CASE i \in 0 .. n /\ i # 0
      <4>1. i-1 \in 0..n /\ i-1 \in 0 .. n+1
        BY <3>3, SMT
      <4>2. QED
        BY <2>2, <3>3, <4>1
    <3>4. CASE i = n+1
      BY <3>4, SMT
    <3>5. QED
      BY <3>2, <3>3, <3>4, SMT
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>3. QED
  BY <1>1, <1>2, NatInduction, Auto

(***************************************************************************)
(* The following theorem asserts that the CHOOSE implicit in a recursive   *)
(* definition of a function with domain 0..n has only one function to      *)
(* choose from.  I don't know if this is of any other use, but it's        *)
(* required as a lemma for proving the next theorem.                       *)
(***************************************************************************)
THEOREM FiniteNatInductiveUnique == 
          ASSUME NEW Def(_,_), NEW n \in Nat, NEW f, NEW h, NEW f0,
                 FiniteNatInductiveDefConclusion(f, f0, Def, n),
                 FiniteNatInductiveDefConclusion(h, f0, Def, n)
          PROVE  h = f
<1> DEFINE P(k) == \A ff, ff0, hh : 
                     FiniteNatInductiveDefConclusion(ff, ff0, Def, k)
                        /\ FiniteNatInductiveDefConclusion(hh, ff0, Def, k)
                     => (hh = ff)
<1>1. P(0)
  <2>1. 0..0 = {0}
    BY SMT
  <2>2. QED
    BY <2>1 DEF FiniteNatInductiveDefConclusion
    
<1>2. ASSUME NEW k \in Nat, P(k)
      PROVE  P(k+1)
  <2>1. SUFFICES ASSUME NEW ff, NEW ff0, NEW hh,
                        FiniteNatInductiveDefConclusion(ff, ff0, Def, k+1),
                        FiniteNatInductiveDefConclusion(hh, ff0, Def, k+1)
                 PROVE  hh = ff
    OBVIOUS
  <2> DEFINE Restrict(g) == [i \in 0..k |-> g[i]]
  <2>2. ASSUME NEW g, FiniteNatInductiveDefConclusion(g, ff0, Def, k+1)
        PROVE  FiniteNatInductiveDefConclusion(Restrict(g), ff0, Def, k)
    <3>1. SUFFICES \A i \in 0..k : Restrict(g)[i] = IF i = 0 THEN ff0 ELSE Def(Restrict(g)[i-1], i)
      BY DEF FiniteNatInductiveDefConclusion
    <3>2. \A i \in 0..(k+1) : g[i] = IF i = 0 THEN ff0 ELSE Def(g[i-1], i)
      BY <2>2 DEF FiniteNatInductiveDefConclusion
    <3>3. /\ 0..k \subseteq 0..(k+1)
          /\ \A i \in 0..(k+1) : (i # 0) => (i-1 \in 0..k)
      BY SMT
    <3> QED
      BY <3>2, <3>3
  <2>3. /\ FiniteNatInductiveDefConclusion(Restrict(ff), ff0, Def, k)
        /\ FiniteNatInductiveDefConclusion(Restrict(hh), ff0, Def, k)
    BY <2>1, <2>2
  <2>4. Restrict(ff) = Restrict(hh)
    BY <2>3, <1>2
  <2>5. SUFFICES \A i \in 0..(k+1) : ff[i] = hh[i]
    BY ONLY <2>1, <2>5 DEF FiniteNatInductiveDefConclusion
  <2>6. \A i \in 0..k : ff[i] = hh[i]
    BY <2>4
  <2>7. ff[k+1] = hh[k+1]
    <3>1. /\ k+1 # 0
          /\ (k+1)-1 \in 0..k
          /\ k+1 \in 0..(k+1)
          /\ (k+1)-1 = k
      BY SMT
    <3>2. QED
      BY ONLY <2>1, <2>6, <3>1 DEF FiniteNatInductiveDefConclusion
  <2>8. QED
    BY <2>6, <2>7, SMT

<1>. HIDE DEF P
<1>3. \A k \in Nat: P(k)
  BY <1>1, <1>2, NatInduction
<1>4. QED
  BY <1>3 DEF P

(***************************************************************************)
(* The following theorem NatInductiveDef is what you use to justify a      *)
(* function defined recursively over the naturals.                         *)
(***************************************************************************)
NatInductiveDefConclusion(f, f0, Def(_,_)) ==
     f = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(f[i-1], i)]
NatInductiveDefHypothesis(f, f0, Def(_,_)) == 
   (f =  CHOOSE g : g = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)])

THEOREM NatInductiveDef ==
          ASSUME NEW Def(_,_), NEW f, NEW f0,
                 NatInductiveDefHypothesis(f, f0, Def)
          PROVE  NatInductiveDefConclusion(f, f0, Def)
<1> SUFFICES \E ff : ff = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(ff[i-1], i)]
 BY DEF NatInductiveDefHypothesis, NatInductiveDefConclusion
<1> DEFINE F(n) == CHOOSE g : g = [i \in 0..n |-> IF i = 0 THEN f0
                                                           ELSE Def(g[i-1], i)]
           ff[n \in Nat] == F(n)[n]
           P(n) == F(n)[n] = IF n = 0 THEN f0
                                      ELSE Def(ff[n-1], n)
<1>2. ASSUME NEW n \in Nat 
      PROVE  FiniteNatInductiveDefConclusion(F(n), f0, Def, n)
  BY FiniteNatInductiveDef, Auto DEF FiniteNatInductiveDefHypothesis
<1>3. \A n \in Nat : P(n)
  <2>1. P(0)
    <3>1. 0 \in 0..0
      BY SMT
    <3>2. QED 
      BY <1>2, <3>1, 0 \in Nat DEF FiniteNatInductiveDefConclusion
  <2>2. ASSUME NEW n \in Nat, P(n)
        PROVE  P(n+1)
    <3>1. F(n+1)[n] = F(n)[n]
      <4> DEFINE g == F(n)
                 h == F(n+1)
                 hh == [i \in 0..n |-> h[i]]
      <4>1. /\ FiniteNatInductiveDefConclusion(g, f0, Def, n)
            /\ FiniteNatInductiveDefConclusion(h, f0, Def, n+1)
        BY <1>2
      <4> HIDE DEF g, h
      <4>2. FiniteNatInductiveDefConclusion(hh, f0, Def, n)
        <5> SUFFICES ASSUME NEW i \in 0..n
                     PROVE  h[i] = IF i=0 THEN f0 ELSE Def(hh[i-1],i)
          BY DEF FiniteNatInductiveDefConclusion
        <5> /\ i \in 0..(n+1)
            /\ 0 \in 0..(n+1)
            /\ (i # 0) => i-1 \in 0..n
          BY SMT
        <5> QED
          BY <4>1 DEF FiniteNatInductiveDefConclusion
      <4>3. g = hh
        BY <4>1, <4>2, FiniteNatInductiveUnique
      <4>4. hh[n] = h[n]
        BY SMT
      <4>5. QED
        BY <4>3, <4>4 DEF g,h
    <3> HIDE DEF F
    <3>2. /\ n+1 \in Nat
          /\ n+1 \in 0..(n+1)
          /\ n+1 # 0
          /\ (n+1)-1 = n
      BY SMT
    <3>3. F(n+1)[n+1] = Def(F(n+1)[n], n+1)
     BY <1>2, <3>2 DEF FiniteNatInductiveDefConclusion 
    <3> QED
      BY <3>1, <3>3
  <2>3. QED
    BY <2>1, <2>2, NatInduction, Auto
<1> HIDE DEF F
<1>4. QED
  BY <1>3

(***************************************************************************)
(* NatInductiveDef says nothing about the type of the recursively defined  *)
(* function.  The following theorem allows you to deduce that type.        *)
(***************************************************************************)
THEOREM NatInductiveDefType ==
           ASSUME NEW Def(_,_), NEW S, NEW f, NEW f0 \in S,
                  NatInductiveDefConclusion(f, f0, Def),
                  f0 \in S,
                  \A v \in S, n \in Nat \ {0} : Def(v, n) \in S
           PROVE  f \in [Nat -> S]
<1> SUFFICES \A n \in Nat : f[n] \in S
  BY DEF NatInductiveDefConclusion
<1> DEFINE P(n) == f[n] \in S
<1>1. P(0)
  BY 0 \in Nat DEF NatInductiveDefConclusion
<1>2. ASSUME NEW n \in Nat, P(n)
      PROVE  P(n+1)
 <2>1. /\ n+1 \in Nat \ {0}
       /\ (n+1)-1 = n
   BY ONLY SMT
 <2>2. QED
   BY <1>2, <2>1 DEF NatInductiveDefConclusion
<1>3. QED
  BY <1>1, <1>2, NatInduction

(***************************************************************************)
(* The following theorem shows uniqueness of a function recursively        *)
(* defined over Nat.                                                       *)
(***************************************************************************)
THEOREM NatInductiveUnique == 
          ASSUME NEW Def(_,_), NEW f, NEW h, NEW f0,
                 NatInductiveDefConclusion(f, f0, Def),
                 NatInductiveDefConclusion(h, f0, Def)
          PROVE  h = f
<1> SUFFICES ASSUME NEW n \in Nat 
             PROVE  h[n] = f[n]
  BY DEF NatInductiveDefConclusion
<1> DEFINE Restrict(g, i) == [j \in 0..i |-> g[j]]
<1>2. ASSUME NEW g, NEW i \in Nat,
             NatInductiveDefConclusion(g, f0, Def)
      PROVE  FiniteNatInductiveDefConclusion(Restrict(g, i), f0, Def, i)
  <2>1. \A j \in 0..i : g[j] = IF j = 0 THEN f0 ELSE Def(g[j-1], j)
    <3>1. 0..i \subseteq Nat
      BY SMT
    <3>2. QED
      BY <1>2, <3>1 DEF NatInductiveDefConclusion
  <2>2. ASSUME NEW j \in 0..i 
        PROVE  Restrict(g,i)[j] = IF j = 0 THEN f0 ELSE Def(Restrict(g,i)[j-1], j)
    <3> /\ 0 \in 0..i
        /\ (j # 0) => j-1 \in 0..i
      BY SMT
    <3> QED
      BY <2>1 
  <2>3. QED
    BY <2>2 DEF FiniteNatInductiveDefConclusion
<1>3. /\ FiniteNatInductiveDefConclusion(Restrict(f, n), f0, Def, n)
      /\ FiniteNatInductiveDefConclusion(Restrict(h, n), f0, Def, n)
  BY <1>2
<1>4. Restrict(f, n) = Restrict(h, n)
  BY <1>3,  FiniteNatInductiveUnique
<1>5. QED
  BY <1>4, SMT

=============================================================================
(***************************************************************************)
(* The following example shows how this module is used.                    *)
(***************************************************************************)

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM FactorialDefConclusion == NatInductiveDefConclusion(factorial, 1, LAMBDA v,n : n*v)
<1>1. NatInductiveDefHypothesis(factorial, 1, LAMBDA v,n : n*v)
  BY DEF NatInductiveDefHypothesis, factorial 
<1>2. QED
  BY <1>1, NatInductiveDef

THEOREM FactorialDef == \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
BY FactorialDefConclusion DEFS NatInductiveDefConclusion

THEOREM FactorialType == factorial \in [Nat -> Nat]
<1>1. \A v \in Nat, n \in Nat \ {0} : n * v \in Nat
  BY SMT
<1>2. QED
  BY <1>1, 1 \in Nat, NatInductiveDefType, FactorialDefConclusion, Auto

=============================================================================
\* Modification History
\* Last modified Wed Nov 21 13:37:52 GMT-03:00 2012 by merz
\* Last modified Sat Nov 26 08:49:59 CET 2011 by merz
\* Last modified Mon Nov 07 08:58:05 PST 2011 by lamport
\* Created Mon Oct 31 02:52:05 PDT 2011 by lamport
