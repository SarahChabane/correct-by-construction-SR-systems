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
require import SRmodel.


(* Useful predicats on a state*)

pred full(A:ioa , s:state) = !exists (s':state), FSet.mem (state_set(A)) s' /\ (FSet.mem (trans_set(A)) (s,ibo,s')).
pred ready (A:ioa, s:state) = exists (s':state), FSet.mem (state_set(A)) s' /\ (FSet.mem (trans_set(A)) (s,bio,s') \/  FSet.mem (trans_set(A)) (s,io,s')).


op steady (A: ioa, s:state) = FSet.mem(trans_set(A))(s,io,s) /\ exists (s':state), FSet.mem(state_set(A)) s' /\ FSet.mem (trans_set(A)) (s,bio,s') /\ !FSet.mem(trans_set(A))(s',io,s').

op frozen (A: ioa, s:state) = FSet.mem(trans_set(A))(s,io,s) /\ exists (s':state), FSet.mem(state_set(A)) s' /\ FSet.mem (trans_set(A)) (s,bio,s') /\ FSet.mem(trans_set(A))(s',io,s').
op delayed (A:ioa, s:state) = !FSet.mem (trans_set(A)) (s,io,s).


op idle (A:ioa, s:state) = FSet.mem(trans_set(A))(s,bibo,s) /\ exists (s':state), FSet.mem(state_set(A)) s' /\ FSet.mem(trans_set(A))(s,bio,s') /\ !is_init A s'.

op  exceed (s:state, n:int) = n < Abstioa.size s .
  

op sequence(A1 A2:ioa,s1 s2:state) = !(delayed A1 s1 /\ frozen A2 s2).

op sequence1(A1 A2:ioa,s1 s2:state) = !(frozen A1 s1 /\ delayed A2 s2).
  
(*Useful operations *)

op extendMem1 (M1 L1 M2 L2:int)  = if M1<L1 then min (L1-M1) M2 else 0.
op extendMem2 (M2 L2:int) = if M2<L2 then L2-M2 else 0.
op exists_trans (A:ioa,t:transition) = FSet.mem(trans_set(A)) t.
op exists_state (A:ioa,s:state) = FSet.mem(state_set(A)) s.
op add_trans_state (a:transition, set:transition fset, set2: state fset) =   ((FSet.fset1 a  `|` set) ,(FSet.fset1 (src a)  `|` FSet.fset1 (dst a)  `|`  set2)).
op sHat (A:ioa, s:state, l:int) = if idle A s /\ !frozen A s /\ 2< Abstioa.size s  then inc s l else s.

(************* composition of states ****************)
(* Adding transitions in set of transitions & states *)

op compose_label(A1 A2:ioa, t1 t2:transition, l1 l2:label,transition_set:transition fset, state_set:state fset, n L1 l :int)   = 

(* Generation of transition i/o *) 
with  l1=io, l2 =io => 
         add_trans_state (((src t1)++(inc (src t2) L1)),io,((dst t1)++(inc (dst t2) L1)))  transition_set state_set 

with  l1 = ibo, l2= bio  =>
         if (exists s1':state, exists_state A1 s1'/\ exists_trans A1 ((src t1),io,s1')/\ exists s2' : state, exists_state A2 s2' 
         /\  exists_trans A2 ((src t2),io,s2') )  then  ( transition_set,state_set)
    else (add_trans_state (((src t1)++(inc (src t2) L1 )),io,((dst t1)++(inc (dst t2) L1)))   transition_set state_set)

(* Generation of transition i/baro*)
with l1 = io,l2=ibo =>
        if ( (sequence A1 A2 (dst t1) (dst t2) ) /\ 
        !exceed ((dst t1)++(dst t2)) n )   
        then add_trans_state (((src t1)++(inc (src t2) L1)),ibo,((dst t1)++(inc (dst t2) L1 )))   transition_set state_set
        else (transition_set,state_set)

with l1=ibo,l2=bibo =>
        if (!exceed ((dst t1)++(dst t2)) n ) /\
        !( (exists s1' : state, exists_state A1 s1'/\ exists_trans A1 ((src t1),io,s1')/\exists s2':state,  exists_state A2 s2' /\  exists_trans A2 ((src t2),ibo,s2') /\ (sequence A1 A2 s1' s2') ))       then 

         add_trans_state (((src t1)++(inc (src t2) L1)),io,((dst t1)++(inc (sHat A2 (dst t2) l) L1)))  transition_set state_set                                                         
        else (transition_set,state_set)

(*Generation of transition bar i/o*)
with l1=bio,l2=io =>
        if ( (sequence A1 A2 (dst t1) (dst t2) ) )         
        then add_trans_state (((src t1)++(inc (src t2) L1)),bio,((dst t1)++(inc (dst t2) L1)))  transition_set  state_set
        else (transition_set,state_set)

with l1=bibo,l2=bio =>
        if  !( (exists s1' : state, exists_state A1 s1'
        /\ exists_trans A1 ((src t1),bio,s1')/\exists s2' : state, 
        exists_state A2 s2' /\  exists_trans A2 ((src t2),io,s2') /\  (sequence A1 A2 s1' s2')) )       
        then add_trans_state (((src t1)++(inc (src t2) L1)),bio,((dst t1)++(inc (dst t2) L1))) transition_set state_set
       else (transition_set,state_set)

(*Generation of transition bar i/bar o*)
with l1= bio,l2= ibo =>
        if idle A2 (src t2) then
        add_trans_state (((src t1)++(inc (src t2) L1)),bibo,((src t1)++(inc (src t2) L1)))  transition_set state_set
        else if delayed A2 (src t2) then
         add_trans_state (((src t1)++(inc (src t2) L1)),bibo,((dst t1)++(inc (dst t2) L1)))  transition_set state_set else (transition_set,state_set)

with l1=bibo,l2=bibo =>
       if idle A2 (src t2) then 
        add_trans_state (((src t1)++(inc (src t2) L1)),bibo,((src t1)++(inc (src t2) L1)))  transition_set state_set
       else
        if !(delayed A2 (src t2) /\  (exists s1':state, exists_state A1 s1'/\exists_trans A1 ((src t1),bio,s1') /\ exists s2' : state, exists_state A2 s2' /\  
        exists_trans A2((src t2),ibo,s2')))
        then add_trans_state ((src t1)++(inc (src t2) L1),bibo,((dst t1)++(inc (dst t2) L1)))   transition_set state_set
        else (transition_set,state_set)
    
(*Not composables *)
with l1=io,l2=bio=>(transition_set,state_set)
with l1=io,l2=bibo=>(transition_set,state_set)
with l1=ibo,l2=io=>(transition_set,state_set)
with l1=ibo,l2=ibo=>(transition_set,state_set)
with l1=bio,l2=bio=>(transition_set,state_set)
with l1=bio, l2=bibo => (transition_set,state_set)
with l1=bibo, l2=io => (transition_set,state_set)
with l1=bibo, l2=ibo=>(transition_set,state_set).

  (* Composition of states using compose_label *)

op compose_state (A1 A2 : ioa, t1 t2:transition, transitions:transition fset, states:state fset, n L1 l: int) =
let l1=extractlabel t1 in let
  l2 = extractlabel t2 in
  compose_label A1 A2 t1 t2 l1 l2 transitions states n L1 l.
 
module Safe_composition = {
  var exM1, exM2 : int
  var ioA1, ioA2, ioA: ioa
  var transitions : transition fset
  var states : state fset
proc rules(A1:ioa,A2:ioa, L1:int, M1 :int, L2:int, M2 :int):ioa={
  var transitions1,transitions2,states1,states2;
  var s01,s02,s0,t1,t2;

    s01 = init_state(A1);
    s02=init_state(A2);
    s0 = (s01++s02);
    states1 = state_set(A1);
    states2 = state_set(A2);
    transitions1 = trans_set(A1);
    while (transitions1 <> fset0){
    t1 = pick transitions1;   
      (*Here to test all transitions of A2 with every transition of A1*)
    transitions2 = trans_set(A2);
    while (transitions2  <> fset0){ 
    t2 = pick transitions2;  
    if (sequence A1 A2 (src t1) (src t2) /\ sequence1 A1 A2 (src t1) (src t2)) 
       { (transitions,states) = compose_state A1 A2  t1 t2  
          transitions states (M1 +M2) L1 L2;

         transitions2 = transitions2 `\` fset1 t2;
        }
      }
       transitions1 = transitions1 `\` fset1 t1;
 }     
  return (s0,states,transitions); 
}


 proc composition(M1:int, L1:int, M2:int, L2:int):ioa =
 {
    exM1 = M1 + extendMem1 M1 L1 M2 L2;
    exM2 = M2 + extendMem2 M2 L2;
    ioA1 = SR.construct_model (exM1,L1);
    ioA2 = SR.construct_model (exM2,L2);
    ioA = rules(ioA1,ioA2, L1, M1 , L2, M2);
    return ioA; 
    }

}.

(*** No state exceed the value of memory *)

lemma not_exceed : forall (m1 l1 m2 l2 :int), hoare[Safe_composition.composition :  0<m1 /\ 0<m2 /\ 0<l1 /\ 0<l2 /\ m1=M1 /\ l1=L1 /\ m2=M2 /\ l2=L2  ==> forall (s:state), mem (state_set res) s => !(exceed s (m1+m2)) ]. 
    proof.
    move => m1 l1 m2 l2.
      proc*.
    inline*.
      sp.
      wp.
      
    while(true).    
      sp.
      wp.
     while(true).    
      auto;smt(@FSet).
      auto;progress;smt(@FSet).
      wp.
      while(forall (s:state), mem Safe_composition.states s => !(exceed s (M1+M2))).    
      auto;smt(@FSet). sp. wp.
         while(forall (s:state), mem Safe_composition.states s => !(exceed s (M1+M2))).
      auto;smt(@FSet). auto;progress. smt timeout=10.  rewrite H4. smt w=(@SRmodel) timeout=10.
smt.
  qed.

(***** The composition of two well formed SR-models is wellformed *****)
lemma well_formed : forall (m1 l1 m2 l2 : int), hoare[Safe_composition.composition : 0<m1 /\ 0<m2 /\ 0<l1 /\ 0<l2 /\ m1=M1 /\ l1=L1 /\ m2=M2 /\ l2=L2 ==>(is_wellformed Safe_composition.ioA1 m1 l1  ) /\( is_wellformed Safe_composition.ioA2 m2 l2) => is_wellformed res (m1+m2) (l1+l2)].
  proof.
    move => m1 l1 m2 l2.
      proc*.
    inline*.
      sp.
      wp.
      
    while(true).    
      sp.
      wp.
     while(true).    
      auto;smt(@FSet).
      auto;progress;smt(@FSet).
      wp.
      while(forall (s:state), mem Safe_composition.states s => !(exceed s (M1+M2))).    
      auto;smt(@FSet). sp. wp.
         while(forall (s:state), mem Safe_composition.states s => !(exceed s (M1+M2))).
    auto;smt(@FSet). auto;progress. smt timeout=10.  auto;smt(@SRmodel).  auto;smt(@SRmodel).
   auto;smt(@SRmodel).  auto;smt(@SRmodel). auto;smt(@SRmodel).   auto;smt(@SRmodel).  auto;smt(@SRmodel). 

  qed.
