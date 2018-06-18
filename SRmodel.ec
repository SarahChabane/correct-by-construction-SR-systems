(**************************************************************************)
(*                                                                        *)
(*  Correct By construction Synchronous reactive systems                  *)
(*  Copyright (C) 2018                                                    *)
(*  Sarah Chabane               &   Rabea Ameur-Boulifa                   *)
(*  Limose Laboratory-Boumerdes     LTCI-Télécom ParisTech                *)(**************************************************************************)
 
require import AllCore.
require import Int.
require import FSet.
require import List.
require import Abstioa.



(* Construction of SR-model *)
type state = int list state.
type transition = state transition.
type ioa = state ioa.


(*Remove an element from a state*)
op remov (i:int, s:state ) = List.rem i s.

(*Extend a state with a new element*)
op extend(i:int, s:state) = List.rcons  s i.

(* Incrementating all data of a state*)
op inc(s:state, l:int) = 
   with s = [] => []
   with s = hd::ls => 
              if hd=l then hd::inc ls l else (hd+1)::inc ls l. 

(* Return the value of the oldest data of a state*)

 op oldest_data (s:state) =
 with s =[] => 0
 with s = hd :: ls =>  max hd (oldest_data ls).
 
op oldest2_data(s:state) = oldest_data(remov (oldest_data s) s).



op equiv_states (n:int,s1 s2:state) =
  with s1 = [], s2=[] => true
  with s1 =[], s2=hd2::ls2 => false
  with s1=hd1::ls1, s2 = []=> false
  with s1=hd1::ls1, s2 = hd2::ls2 => 
 if (hd1=hd2 \/ (n <= hd1 /\ n <= hd2 )) 
 then equiv_states (n-1) ls1 ls2  else false.

op exists_equiv(n:int,s:state, set:state fset) =  exists (s1:state), (mem set s1)  /\ equiv_states n s s1.

op set_equiv(n:int, s:state, set:state fset)= 
  oflist (filter (predC (equiv_states n s)) (elems set)).


axiom size(s:state): Abstioa.size s = List.size s.

module SR = {
  var statesAutomata : state fset
  var unexp : state fset
  var transitions : transition fset
  var s0 : state

  proc construct_model(M:int,L:int): ioa ={
  var s, s1, s2, s2',s3; 
    statesAutomata= FSet.fset0;
    unexp= FSet.fset0;
    transitions = FSet.fset0;
    s0 = []; 
    statesAutomata = FSet.fset1 s0 ;
    transitions = FSet.fset1 (s0,bibo,s0) `|` transitions;
    s1=  (extend 1 s0) ;
    transitions = FSet.fset1 (s0,ibo,s1) `|` transitions;  
    unexp = FSet.fset1 s1 `|` unexp;
    s=s1;
    while (unexp <> FSet.fset0 ){
    s = pick unexp;

    if (Abstioa.size s <M) {
    s2= extend 1 (inc s L)   ;
       if (exists_equiv L s2 statesAutomata)
       s2= pick (set_equiv L s2 statesAutomata); 
       transitions = FSet.fset1 (s,ibo,s2) `|` transitions;
       if (!mem statesAutomata s2)
          unexp = FSet.fset1 s2 `|` unexp;
                  }
     if (oldest_data s = L ){ 
     s2 = extend 1 (inc(remov (oldest_data s) s) L);
     if (exists_equiv L s1 statesAutomata)
     s2= pick (set_equiv L s2 statesAutomata);
     transitions = FSet.fset1 (s,io,s2) `|` transitions;
     if (!mem statesAutomata s2)
          unexp  = FSet.fset1 s2 `|` unexp;
     s2' = inc(remov (oldest_data s) s) L;
     if (exists_equiv L s2' statesAutomata)
      s2'= pick (set_equiv L s2' statesAutomata);
      transitions = FSet.fset1 (s,bio,s2') `|` transitions;
      if (!mem statesAutomata s2')
       unexp  = FSet.fset1 s2' `|` unexp;
      if ((2 <= Abstioa.size s)  /\  1<(oldest_data s - oldest2_data s)){
      s3=inc s L;
      if (exists_equiv L s3 statesAutomata)
      s3= pick (set_equiv L s3 statesAutomata);
      transitions = FSet.fset1 (s,bibo,s3) `|` transitions;
      if (!mem statesAutomata s3)
      unexp  = FSet.fset1 s3 `|` unexp;
      }
      else
      transitions = FSet.fset1 (s,bibo,s) `|` transitions;
   }
      else
      {  
      s2 = inc s L;
      if (exists_equiv L s2 statesAutomata)
      s2= pick (set_equiv L s2 statesAutomata);
      transitions = FSet.fset1 (s,bibo,s2) `|` transitions;
      if (!mem statesAutomata s2){
      unexp  = FSet.fset1 s2 `|` unexp;
      }} 
      unexp =  unexp `\` FSet.fset1 s;
      statesAutomata = FSet.fset1 s `|` statesAutomata;

      } 
return (s0,statesAutomata,transitions);  
}}.

(*Useful axioms on operations *)

axiom extractlabelT(t:transition) : forall (s1 s2 : state, l:label), t=(s1,l,s2) => Abstioa.extractlabel t = l.
axiom extractSrc (t:transition) : forall (s1 s2 : state, l:label), t=(s1,l,s2) => src t = s1.
axiom extractDst (t:transition) : forall (s1 s2 : state, l:label), t=(s1,l,s2) => dst t = s2.
axiom init_stateT (A:ioa):forall (s0:state, st :state fset, tr : transition fset), A=(s0,st,tr) => init_state A = s0. 
axiom state_setT (A:ioa):forall (s0:state, st :state fset, tr : transition fset), A=(s0,st,tr) => state_set A = st.

axiom trans_setT (A:ioa):forall (s0:state, st :state fset, tr : transition fset), A=(s0,st,tr) => trans_set A = tr.

(************ Proof of correctness ************)

(********** Determinism **********)

axiom ax1(L:int): forall(s:state), (((2 <= Abstioa.size s)  /\  1<(oldest_data s - oldest2_data s)) /\ !(oldest_data s = L))  \/ (!((2 <= Abstioa.size s)  /\  1<(oldest_data s - oldest2_data s)) /\ (oldest_data s = L)).

lemma determinism  : forall (m l :int),  hoare[SR.construct_model : 0<m /\ 0<l   ==> is_determinist res].
   proof.
       move => m l.
   proc.
   sp.
   wp.
   while(forall(t1 t2:transition),  mem SR.transitions t1 /\  mem SR.transitions t2 /\ src t1 = src t2 /\ dst t1<>dst t2 =>  ( (extractlabel t1) <> (extractlabel t2))).
  (* rcondt 2;auto.*)
   auto;smt timeout=10.
   auto;smt timeout=10.
   
 qed.


(********** Outing when data ready **********)

lemma out_when_reach_latency :forall(m l :int), hoare[SR.construct_model : 0<m /\ 0<l /\ L=l /\ M=m ==> out_when_ready res l].   proof.
    move => m l.
    proc.
    sp.
    wp.
    while(forall (s:state), mem SR.statesAutomata s /\ oldest_data s = L => (exists(s1:state), mem SR.transitions (s,bio,s1)) /\ (exists (s2:state), mem SR.transitions (s,io,s2))). 
   auto;progress;smt(@FSet).
    auto;progress.
    auto;smt.
      auto;smt.
     auto;smt.
     qed.
   

(********** Accepting Until full **********)

 lemma accept_data_until_full : forall(m l:int),        hoare[SR.construct_model : 0<m /\ 0<l /\ L=l /\ m=M  ==> in_until_full res m].
     proof.
     move => m l.
    proc.
     sp.
     wp.
     while((forall (s:state), mem SR.statesAutomata s /\ Abstioa.size s < M => exists(s':state),mem SR.transitions (s,ibo,s'))).
     auto;progress;smt(@FSet).
     auto;progress. smt.
     auto;smt timeout=10.
   qed.

(********** Receptiveness **********)
lemma receptiveness : forall(m l:int),        hoare[SR.construct_model : 0<m /\ 0<l /\ L=l /\ m=M  ==> is_receptiv res m l].
     proof.
     move => m l.
    proc.
     sp.
     wp.
     while((forall (s:state), mem SR.statesAutomata s /\ Abstioa.size s < M => exists(s':state),mem SR.transitions (s,ibo,s')) /\ ( oldest_data s = L => (exists(s1:state), mem SR.transitions (s,bio,s1)) /\ (exists (s2:state), mem SR.transitions (s,io,s2)))).
     auto;progress;smt(@FSet).
     auto;progress. smt.
     auto;smt timeout=10.
    auto;smt timeout=10.
   auto;smt timeout=10.
   auto;smt timeout=10.
    qed.


(********** Wait the duration of latency before outpouting **********)
lemma count_before_outing : forall(m l:int), hoare[SR.construct_model : 0<m /\ 0<l /\ L=l /\ m=M  ==> count_before_outing res  l].
     proof.
     move => m l.
    proc.
     sp.
     wp.
     while(forall (s:state), ( (oldest_data s = L) => (exists(s1:state), mem SR.transitions (s,bio,s1)) /\ (exists (s2:state), mem SR.transitions (s,io,s2)))).
     auto;progress;smt(@FSet).
     auto;progress. smt.
     auto;smt timeout=10.
    auto;smt timeout=10.
    qed.

(********** No idle before end of computation **********)

lemma idleness :  forall (m l : int), hoare[SR.construct_model : 0<m /\ 0<l ==> no_idle res l].
proof.
      move => m l.
      proc.
      sp.
      wp.
      while(forall (s:state), (mem SR.statesAutomata s /\  !(oldest_data s = L)) => exists (s':state), (mem SR.transitions (s,bibo,s')  )).
      auto;progress;smt(@FSet).
      auto;progress. smt. auto;smt.
qed.
   

(**********Well-formed SR-model **********)

lemma well_formed : forall(m l:int), hoare[SR.construct_model : 0<m /\ 0<l /\ L=l /\ m=M  ==> is_wellformed res m l].
 proof.
    move => m l.
      proc.
      sp.
   wp.
   
      while((forall(t1 t2:transition),  mem SR.transitions t1 /\  mem SR.transitions t2 /\ src t1 = src t2 /\ dst t1<>dst t2 =>  ( (extractlabel t1) <> (extractlabel t2)))   \/ (forall (s:state), mem SR.statesAutomata s /\ Abstioa.size s < M => exists(s':state),mem SR.transitions (s,ibo,s')) \/ (forall (s:state), mem SR.statesAutomata s /\ oldest_data s = L => (exists(s1:state), mem SR.transitions (s,bio,s1)) \/ (exists (s2:state), mem SR.transitions (s,io,s2))) \/ (forall (s:state), (mem SR.statesAutomata s /\  !(oldest_data s = L)) => exists (s':state), (mem SR.transitions (s,bibo,s')  ))).
      auto;progress;smt timeout=10.
      auto;smt timeout=10.

   qed.
