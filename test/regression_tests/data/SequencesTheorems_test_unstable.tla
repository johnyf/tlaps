------------------------ MODULE SequencesTheorems_test -----------------------
(***************************************************************************)
(* This module is a library of theorems about sequences and the            *)
(* corresponding operations.                                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLAPS, NaturalsInduction

(***************************************************************************)
(* Elementary properties about Seq(S)                                      *)
(***************************************************************************)

THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
BY SMT

THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
BY SMT

THEOREM LenProperties == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
         /\ DOMAIN seq = 1 .. Len(seq) 
BY SMT

THEOREM ExceptSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq), NEW e \in S
  PROVE  /\ [seq EXCEPT ![i] = e] \in Seq(S)
         /\ Len([seq EXCEPT ![i] = e]) = Len(seq)
         /\ \A j \in 1 .. Len(seq) : [seq EXCEPT ![i] = e][j] = IF j=i THEN e ELSE seq[j]
\* 2013-06-12: SMT doesn't prove this by itself
<1>. DEFINE exc == [seq EXCEPT ![i] = e]
<1>1. Len(exc) = Len(seq)
  BY SMT
<1>2. DOMAIN exc = 1 .. Len(seq)
  BY SMT
<1>3. \A j \in 1 .. Len(seq) : exc[j] = IF j=i THEN e ELSE seq[j]
  BY SMT, <1>2
<1>4. exc \in Seq(S)
  <2>2. \A j \in DOMAIN exc : exc[j] \in S
    BY SMT, <1>2, <1>3
  <2>. QED
    BY SMT, <1>2, <2>2
<1>. QED
  BY <1>1, <1>3, <1>4

THEOREM IsASeq ==
  ASSUME NEW n \in Nat, NEW e(_), NEW S,
         \A i \in 1..n : e(i) \in S
  PROVE  [i \in 1..n |-> e(i)] \in Seq(S)
PROOF OMITTED  \* SMT should prove this!

(***************************************************************************
                 Concatenation (\o) And Properties                      
***************************************************************************)

THEOREM ConcatProperties ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  /\ s1 \o s2 \in Seq(S)
         /\ Len(s1 \o s2) = Len(s1) + Len(s2)
         /\ \A i \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[i] =
                     IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
BY SMT

THEOREM ConcatEmptySeq ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ seq \o << >> = seq
         /\ << >> \o seq = seq
BY SMT

THEOREM ConcatAssociative ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S), NEW s3 \in Seq(S)
  PROVE  (s1 \o s2) \o s3 = s1 \o (s2 \o s3)
BY SMT

(***************************************************************************)
(*                     SubSeq, Head and Tail                               *)
(***************************************************************************)

THEOREM SubSeqProperties ==
  ASSUME NEW S,
         NEW s \in Seq(S),
         NEW m \in 1 .. Len(s)+1,
         NEW n \in m-1 .. Len(s)
  PROVE  /\ SubSeq(s,m,n) \in Seq(S)
         /\ Len(SubSeq(s, m, n)) = n-m+1
         /\ \A i \in 1 .. n-m+1 : SubSeq(s,m,n)[i] = s[m+i-1]
<1>1. CASE n \in m .. Len(s)
  BY <1>1, SMT
<1>2. CASE n = m-1
  <2>. DEFINE sub == SubSeq(s,m,m-1)
  <2>1. sub = [i \in 1..0 |-> s[i]]
    BY SMT
  <2>2. Len(sub) = n-m+1
    BY <1>2, <2>1, SMT
  <2>3. \A i \in 1..0 : sub[i] \in S
    BY SMT
  <2>4. \A i \in 1 .. n-m+1 : SubSeq(s,m,n)[i] = s[m+i-1]
    BY <1>2, SMT
  <2>. QED
    BY <1>2, <2>1, <2>2, <2>3, <2>4, IsASeq
<1>. QED
  BY <1>1, <1>2, SMT

THEOREM HeadAndTailOfSeq ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
          /\ Len(Tail(seq)) = Len(seq)-1
          /\ \A i \in 1 .. Len(Tail(seq)) : Tail(seq)[i] = seq[i+1]
BY SMT
  (*************************************************************************)
  (* Note: the way Tail is defined, Tail(<< >>) \in Seq(S) is actually     *)
  (* valid (because Tail(<< >>) = << >>).                                  *)
  (*************************************************************************)

THEOREM TailIsSubSeq ==
  ASSUME NEW S,
         NEW seq \in Seq(S), seq # << >>
  PROVE  Tail(seq) = SubSeq(seq, 2, Len(seq))
BY SMT

THEOREM SubSeqRecursiveFirst ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  SubSeq(seq, m, n) = << seq[m] >> \o SubSeq(seq, m+1, n)
BY SMT

THEOREM SubSeqRecursiveSecond ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  SubSeq(seq, m, n) = SubSeq(seq, m, n-1) \o << seq[n] >>
<1>. DEFINE lhs == SubSeq(seq, m, n)
<1>. DEFINE rhs == SubSeq(seq, m, n-1) \o << seq[n] >>
<1>1. /\ lhs \in Seq(S)
      /\ rhs \in Seq(S)
  BY SMT
<1>2. Len(lhs) = Len(rhs)
  BY SMT
<1>3. ASSUME NEW i \in 1 .. Len(lhs)
      PROVE  lhs[i] = rhs[i]
  <2>1. lhs[i] = seq[m+i-1]
    BY SMT
  <2>2. rhs[i] = seq[m+i-1]
    <3>1. CASE i \in 1 .. Len(lhs)-1
      BY <3>1, SMT
    <3>2. CASE i = Len(lhs)
      <4>1. /\ SubSeq(seq, m, n-1) \in Seq(S)
            /\ << seq[n] >> \in Seq(S)
        BY SMT
      <4>2. i \in 1 .. Len(SubSeq(seq, m, n-1)) + Len(<<seq[n]>>)
        BY SMT
      <4>3. ~(i <= Len(SubSeq(seq, m, n-1)))
        BY <3>2, SMT
      <4>4. rhs[i] = <<seq[n]>>[i - Len(SubSeq(seq, m, n-1))]
        BY <4>1, <4>2, <4>3, ConcatProperties
      <4>5. i - Len(SubSeq(seq, m, n-1)) = 1
        BY <3>2, SMT
      <4>6. rhs[i] = seq[n]
        BY <4>4, <4>5
      <4>. QED
        BY <3>2, <4>6, SMT
    <3>3. QED
      BY <3>1, <3>2, SMT
  <2>. QED
    BY <2>1, <2>2
<1>. QED
  BY <1>1, <1>2, <1>3, SMT

(***************************************************************************)
(*                 Append, InsertAt, Cons & RemoveAt                       *)
(* Append(seq, elt) appends element elt at the end of sequence seq         *)
(* Cons(elt, seq) prepends element elt at the beginning of sequence seq    *)
(* InsertAt(seq, i, elt) inserts element elt in the position i and pushes  *)
(* the                                                                     *)
(*                        original element at i to i+1 and so on           *)
(* RemoveAt(seq, i) removes the element at position i                      *)
(***************************************************************************)

THEOREM AppendProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  /\ Append(seq, elt) \in Seq(S)
         /\ Len(Append(seq, elt)) = Len(seq)+1
         /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
         /\ Append(seq, elt)[Len(seq)+1] = elt
BY SMT

THEOREM AppendIsConcat ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  Append(seq, elt) = seq \o <<elt>>
BY SMT

Cons(elt, seq) == <<elt>> \o seq

THEOREM ConsProperties ==
          ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
          PROVE /\ Cons(elt, seq) \in Seq(S)
                /\ Len(Cons(elt, seq)) = Len(seq)+1
                /\ Cons(elt, seq)[1] = elt
                /\ \A i \in 1 .. Len(seq) : Cons(elt, seq)[i+1] = seq[i]
BY SMT DEF Cons

THEOREM ConsEmpty ==
  \A x : Cons(x, << >>) = << x >>
BY SMT DEF Cons

THEOREM ConsHeadTail ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Cons(Head(seq), Tail(seq)) = seq
BY SMT DEF Cons

InsertAt(seq,i,elt) == SubSeq(seq, 1, i-1) \o <<elt>> \o SubSeq(seq, i, Len(seq))

THEOREM InsertAtProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq)+1, NEW elt \in S
  PROVE  /\ InsertAt(seq,i,elt) \in Seq(S)
         /\ Len(InsertAt(seq,i,elt)) = Len(seq)+1
         /\ \A j \in 1 .. Len(seq)+1 : InsertAt(seq,i,elt)[j] =
                     IF j<i THEN seq[j]
                     ELSE IF j=i THEN elt
                     ELSE seq[j-1]
(* The following worked on 2013-06-11 but not on 2013-06-12
   BY SMT, SubSeqProperties DEF InsertAt
*)
<1>1. InsertAt(seq,i,elt) \in Seq(S)
  BY SMT, SubSeqProperties DEF InsertAt
<1>2. Len(InsertAt(seq,i,elt)) = Len(seq)+1
  BY SMT DEF InsertAt
<1>3. ASSUME NEW j \in 1 .. Len(seq)+1
      PROVE  InsertAt(seq,i,elt)[j] = IF j<i THEN seq[j]
                                      ELSE IF j=i THEN elt
                                      ELSE seq[j-1]
  <2>1. CASE j \in 1 .. i-1
    BY <2>1, SMT DEF InsertAt
  <2>2. CASE j = i  \** I don't understand why this case makes problems but not the others
    <3>1. j - Len(SubSeq(seq, 1, i-1)) = 1
      BY <2>2, SMT
    <3>2. <<elt>>[j - Len(SubSeq(seq, 1, i-1))] = elt
      BY <3>1  \** SMT doesn't work here
    <3>3. (SubSeq(seq, 1, i-1) \o <<elt>>)[j] = elt
      BY <2>2, <3>2, SMT
    <3>. QED
      BY <2>2, <3>3, SMT DEF InsertAt
  <2>3. CASE j \in i+1 .. Len(seq)+1
    BY <2>3, SMT DEF InsertAt
  <2>. QED
    BY <2>1, <2>2, <2>3, SMT
<1>. QED
  BY <1>1, <1>2, <1>3

RemoveAt(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

THEOREM RemoveAtProperties ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE  /\ RemoveAt(seq,i) \in Seq(S)
          /\ Len(RemoveAt(seq,i)) = Len(seq) - 1
          /\ \A j \in 1 .. Len(seq)-1 : RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]
(* The following worked on 2013-06-11 but not on 2013-06-12
   BY SMT, SubSeqProperties DEF RemoveAt
*)
<1>1. RemoveAt(seq,i) \in Seq(S)
  BY SMT DEF RemoveAt
<1>2. Len(RemoveAt(seq,i)) = Len(seq) - 1
  BY SMT DEF RemoveAt
<1>3. ASSUME NEW j \in 1 .. Len(seq)-1
      PROVE  RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]
  <2>1. CASE j \in 1 .. i-1
    BY <2>1, SMT DEF RemoveAt
  <2>2. CASE j \in i .. Len(seq)-1
    <3>0. /\ SubSeq(seq, 1, i-1) \in Seq(S)
          /\ SubSeq(seq, i+1, Len(seq)) \in Seq(S)
      BY SubSeqProperties, SMT
    <3>1. j \in 1 .. Len(SubSeq(seq, 1, i-1)) + Len(SubSeq(seq, i+1, Len(seq)))
      BY SMT
    <3>2. ~(j <= Len(SubSeq(seq, 1, i-1)))
      BY <2>2, SMT
    <3>3. RemoveAt(seq,i)[j] = SubSeq(seq, i+1, Len(seq))[j - Len(SubSeq(seq, 1, i-1))]
      BY <3>0, <3>1, <3>2, ConcatProperties DEF RemoveAt
    <3>. QED
      BY <2>2, <3>3, SMT
  <2>. QED
    BY SMT, <2>1, <2>2
<1>. QED
  BY <1>1, <1>2, <1>3

(***************************************************************************)
(*            Front & Last                                                 *)
(*                                                                         *)
(*  Front(seq)   sequence formed by removing the last element              *)
(*  Last(seq)    last element of the sequence                              *)
(*                                                                         *)
(*  These operators are to Append what Head and Tail are to Cons.          *)
(***************************************************************************)

Front(seq) == SubSeq(seq, 1, Len(seq)-1)
Last(seq) == seq[Len(seq)]

THEOREM FrontLastProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  /\ Front(seq) \in Seq(S)
         /\ Last(seq) \in S 
         /\ Append(Front(seq), Last(seq)) = seq 
         /\ Len(Front(seq)) = Len(seq)-1                    
BY SMT, SubSeqProperties DEF Front, Last

(***************************************************************************)
(* As a corollary of the previous theorem it follows that a sequence is    *)
(* either empty or can be obtained by appending an element to a sequence.  *)
(***************************************************************************)
THEOREM SequenceEmptyOrAppend == 
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE \E s \in Seq(S), elt \in S : seq = Append(s, elt)
BY FrontLastProperties
     
(***************************************************************************)
(*                   REVERSE SEQUENCE And Properties                       *)
(*    Reverse(seq) --> Reverses the sequence seq                           *)
(***************************************************************************)

Reverse(seq) == [j \in 1..(Len(seq)) |-> seq[Len(seq)-j+1] ]

THEOREM ReverseProperties ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Reverse(seq) \in Seq(S)
         /\ Len(Reverse(seq)) = Len(seq)
         /\ Reverse(Reverse(seq)) = seq
<1>1. Reverse(seq) \in Seq(S)
  <2>1. \A j \in 1..Len(seq) : seq[Len(seq)-j+1] \in S
    BY SMT
  <2>2. Reverse(seq) \in [1..Len(seq) -> S]
    BY <2>1, SMT DEF Reverse 
  <2>3. QED
    BY <2>1, <2>2, SMT
<1>2. /\ Len(Reverse(seq)) = Len(seq)
      /\ Reverse(Reverse(seq)) = seq
  BY SMT DEF Reverse
<1>3. QED
  BY <1>1, <1>2

THEOREM ReverseEmpty == Reverse(<< >>) = << >>
BY SMT DEF Reverse

THEOREM ReverseConcat == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Reverse(s1 \o s2) = Reverse(s2) \o Reverse(s1)
BY SMT DEF Reverse

THEOREM ReverseAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Append(seq,e)) = Cons(e, Reverse(seq))
BY SMT DEF Reverse, Cons

THEOREM ReverseCons ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Cons(e,seq)) = Append(Reverse(seq), e)
BY SMT, ConsProperties DEF Reverse
     
THEOREM ReverseSingleton == \A x : Reverse(<< x >>) = << x >>
\* 2013-06-10: "BY SMT DEF Reverse" doesn't prove this
<1> TAKE x
<1>. /\ << >> \in Seq({x})
     /\ << x >> \in Seq({x})
  OBVIOUS
<1>1. << x >> = Cons(x, << >>)
  BY ConsEmpty
<1>2. Reverse(Cons(x, << >>)) = Append(Reverse(<< >>), x)
  BY ReverseCons
<1>3. QED
  BY <1>1, <1>2, ReverseEmpty

THEOREM ReverseSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1..Len(seq), NEW n \in 1..Len(seq)
  PROVE  Reverse(SubSeq(seq, m , n)) = SubSeq(Reverse(seq), Len(seq)-n+1, Len(seq)-m+1)
(* This proof worked on 2013-06-11, but not on 2013-06-12:
   BY SMT, SubSeqProperties DEF Reverse
*)


THEOREM ReversePalindrome ==
  ASSUME NEW S, NEW seq \in Seq(S),
         Reverse(seq) = seq
  PROVE  Reverse(seq \o seq) = seq \o seq
BY ReverseConcat

THEOREM LastEqualsHeadOfReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Last(seq) = Head(Reverse(seq))
BY SMT DEF Last, Reverse

THEOREM FrontEqualsReverseOfTail ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Front(seq) = Reverse(Tail(Reverse(seq)))
BY SMT DEF Front, Reverse

(***************************************************************************)
(* Induction principles for sequences                                      *)
(***************************************************************************)

THEOREM SequencesInductionAppend ==
  ASSUME NEW P(_), NEW S, 
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Append(s,e))
  PROVE  \A seq \in Seq(S) : P(seq)
<1>. DEFINE Q(n) == \A seq \in Seq(S) : Len(seq) = n => P(seq)
<1>1. SUFFICES \A k \in Nat : Q(k)
  OBVIOUS
<1>2. Q(0)
  OBVIOUS
<1>3. ASSUME NEW n \in Nat, Q(n)
      PROVE  Q(n+1)
  <2>1. ASSUME NEW s \in Seq(S), Len(s) = n+1
        PROVE P(s)
    <3>1. /\ Front(s) \in Seq(S)
          /\ Last(s) \in S
          /\ Len(Front(s)) = n
          /\ Append(Front(s), Last(s)) = s
      BY SMT, <2>1, FrontLastProperties 
    <3>2. P(Front(s))
      BY <1>3, <3>1
    <3>3. QED
      BY <3>1, <3>2                  
  <2>. QED
    BY <2>1          
<1>4. QED
  BY <1>2, <1>3, NatInduction
      
THEOREM SequencesInductionCons == 
        ASSUME NEW P(_), NEW S,
               P(<< >>),
               \A s \in Seq(S), e \in S : P(s) => P(Cons(e,s))
        PROVE \A seq \in Seq(S) : P(seq)
<1>. DEFINE Q(n) == \A seq \in Seq(S) : Len(seq) = n => P(seq)
<1>1. SUFFICES \A k \in Nat : Q(k)
  OBVIOUS
<1>2. Q(0)
  OBVIOUS
<1>3. ASSUME NEW n \in Nat, Q(n)
      PROVE  Q(n+1)
  <2>1. ASSUME NEW s \in Seq(S), Len(s) = n+1
        PROVE P(s)
    <3>1. /\ Tail(s) \in Seq(S)
          /\ Head(s) \in S
          /\ Len(Tail(s)) = n
          /\ Cons(Head(s), Tail(s)) = s
      BY SMT, <2>1, ConsHeadTail 
    <3>2. P(Tail(s))
      BY <1>3, <3>1
    <3>3. QED
      BY <3>1, <3>2                  
  <2>. QED
    BY <2>1          
<1>4. QED
  BY <1>2, <1>3, NatInduction

(***************************************************************************)
(*                          RANGE OF SEQUENCE                              *)
(***************************************************************************)

(* The following definition makes sense for any functions, in particular for sequences. *)
Range(f) == { f[i] : i \in DOMAIN f }

RangeSequence(seq) == { seq[i] : i \in 1..Len(seq) }
RangeSequence1(seq, S) == { x \in S : \E i \in 1..Len(seq) : x=seq[i] } 


THEOREM RangeOfSeq == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  Range(seq) \in SUBSET S
BY SMT DEF Range

\* Both the definitions of range, ie. Range and RangeSequence1 are equivalent.
THEOREM RangeEquality == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(seq) = { seq[i] : i \in 1 .. Len(seq) }
<1>1. DOMAIN seq = 1 .. Len(seq)
  BY SMT
<1>2. QED
  BY <1>1 DEF Range

(* The range of the mirror sequence equals that of the original one. *)
THEOREM RangeReverse == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(Reverse(seq)) = Range(seq)
<1>1. Range(Reverse(seq)) \subseteq Range(seq)
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(seq)
                 PROVE  Reverse(seq)[i] \in Range(seq)
    BY SMT, ReverseProperties, RangeEquality
  <2>2. Len(seq)-i+1 \in 1 .. Len(seq)
    BY SMT, <2>1
  <2>. QED
    BY <2>2, RangeEquality DEF Reverse
<1>2. Range(seq) \subseteq Range(Reverse(seq))
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(seq)
                 PROVE  seq[i] \in Range(Reverse(seq))
    BY RangeEquality
  <2>2. Len(seq)-i+1 \in 1 .. Len(seq)
    BY SMT, <2>1
  <2>. QED
    BY SMT, <2>2, RangeEquality, ReverseProperties DEF Reverse
<1>3. QED
  BY <1>1, <1>2

(* Range of concatenation of sequences is union of range of sequences *)
THEOREM RangeConcatenation == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Range(s1 \o s2) = Range(s1) \cup Range(s2)
<1>1. Range(s1) \subseteq Range(s1 \o s2)
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(s1)
                 PROVE  s1[i] \in Range(s1 \o s2)
    BY RangeEquality, Isa
  <2>. QED
    BY SMT, RangeEquality
<1>2. Range(s2) \subseteq Range(s1 \o s2)
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(s2)
                 PROVE  s2[i] \in Range(s1 \o s2)
    BY RangeEquality, Isa
  <2>2. /\ Len(s1)+i \in 1 .. Len(s1 \o s2)
        /\ (s1 \o s2)[Len(s1)+i] = s2[i]
    BY SMT
  <2>. QED
    BY SMT, <2>2, RangeEquality
<1>3. Range(s1 \o s2) \subseteq Range(s1) \cup Range(s2)
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(s1 \o s2)
                 PROVE  (s1 \o s2)[i] \in Range(s1) \cup Range(s2)
    BY LenProperties, ConcatProperties DEF Range
  <2>2. CASE i \in 1 .. Len(s1)
    BY SMT, RangeEquality
  <2>3. CASE i \in Len(s1)+1 .. Len(s1 \o s2)
    BY SMT, RangeEquality
  <2>. QED
    BY <2>2, <2>3, SMT
<1>. QED
  BY <1>1, <1>2, <1>3

=============================================================================
