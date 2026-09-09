From hahn Require Import Hahn. 
Require Import Events.
Require Import Execution.
Require Import value.

Set Implicit Arguments.

Module ConcreteValue <: ValueSig.

  Definition t := value.
  Definition eq_dec := value_eq_dec.

  (* IMM gives every location an initial write.  We interpret that write as
    saying that the location has not yet been allocated. *)
  Definition init : t := VUnalloc.

End ConcreteValue.

Module MemoryModel (Ev : Events ConcreteValue).

  Module Import Ex := Execution ConcreteValue Ev.

  Definition read_label
      (x : Ev.location) (ord : Ev.mode) (v : ConcreteValue.t) : Ev.label :=
    Ev.Aload false ord x v.

  Definition write_label
      (x : Ev.location) (ord : Ev.mode) (v : ConcreteValue.t) : Ev.label :=
    Ev.Astore Ev.Xpln ord x v.

Inductive memory_action : Type :=
| MRead      : Ev.thread_id -> Ev.location -> Ev.mode -> ConcreteValue.t -> memory_action
| MWrite     : Ev.thread_id -> Ev.location -> Ev.mode -> ConcreteValue.t -> memory_action
| MReadFail  : Ev.thread_id -> Ev.location -> memory_action
| MWriteFail : Ev.thread_id -> Ev.location -> memory_action
| MMalloc    : Ev.thread_id -> Ev.location -> memory_action
| MFree      : Ev.thread_id -> Ev.location -> memory_action.

  Definition initial_execution : execution :=
    {| acts_set :=
         fun e =>
           match e with
           | Ev.InitEvent _ => True
           | Ev.ThreadEvent _ _ => False
           end;
       threads_set := fun thread => thread = Ev.tid_init;
       lab :=
         fun e =>
           match e with
           | Ev.InitEvent x => write_label x Ev.Opln VUnalloc
           (*TODO: I don't know how I feel about this work-around... *)
           | Ev.ThreadEvent _ _ => Ev.Afence Ev.Opln
           end;
       rmw := ∅₂;
       data := ∅₂;
       addr := ∅₂;
       ctrl := ∅₂;
       rmw_dep := ∅₂;
       rf := ∅₂;
       co := ∅₂ |}.

  Record extends_execution (G G' : execution) (e : Ev.actid) : Prop := {
    extends_G': acts_set G' e; 
    extends_fresh :
      ~ acts_set G e;
    extends_acts :
      forall a, acts_set G' a <-> acts_set G a \/ a = e;
    extends_lab :
      forall a, acts_set G a -> lab G' a = lab G a;
    (* Ensures e is the 'maximal' action in thread tid. *)
    extends_sb :
      forall a,
        acts_set G a ->
        Ev.tid a = Ev.tid e ->
        Ev.ext_sb a e
  }.
      
  Definition coherence_maximal_write (G: execution) (x: Ev.location) := fun w =>
    acts_set G w /\
    Ev.is_w (lab G) w = true /\
    Ev.loc (lab G) w = Some x /\
    ~ exists w',
        acts_set G w' /\
        Ev.is_w (lab G) w' = true /\
        co G w w'
  .

  Definition isAllocated (G : execution) (x : Ev.location) : Prop :=
    exists w v,
      coherence_maximal_write G x w /\
      Ev.val (lab G) w = Some v /\
      v <> VUnalloc.

  Definition neverAllocated (G : execution) (x : Ev.location): Prop :=   ~ (isAllocated G x). 

  (* A memory model is the model-specific consistency predicate over the
    execution graphs shared by IMM, RC11, Arm, etc. *)
  Record t := {
    consistent : execution -> Prop;
    consistent_complete :
      forall G, consistent G -> complete G
  }.

  Section WithModel.

  Context (M : t).

  (* Model consistency and structural well-formedness are deliberately kept
    separate in the adapters.  In the imported development, for example,
    [imm_consistent] and [rc11_consistent] do not contain [Wf], whereas
    [ArmConsistent] does.  Generic transitions use the normalized judgment
    below. *)
  Definition valid_execution (G : execution) : Prop :=
    Wf G  /\ consistent M G.


  Inductive memory_step : execution -> memory_action -> execution -> Prop :=
  | Step_MRead :
      forall G G' e thread x ty v,
        valid_execution G ->
        extends_execution G G' e ->
        Ev.tid e = thread ->
        lab G' e = read_label x ty v ->
        v <> VUnalloc ->
        valid_execution G' ->

        memory_step G (MRead thread x ty v) G'

  | Step_MWrite :
      forall G G' e thread x ty v,
        valid_execution G ->
        isAllocated G x ->
        extends_execution G G' e ->
        Ev.tid e = thread ->
        lab G' e = write_label x ty v ->
        valid_execution G' ->

        memory_step G (MWrite thread x ty v) G'

  | Step_MReadFail :
      forall G G' e thread x ty,
        valid_execution G ->
        ~ isAllocated G x ->
        extends_execution G G' e ->
        Ev.tid e = thread ->
        lab G' e = read_label x ty VUnalloc ->
        valid_execution G' ->

        memory_step G (MReadFail thread x) G'

  | Step_MWriteFail :
      forall G G' e thread x ty v,
        valid_execution G ->
        ~ isAllocated G x ->
        extends_execution G G' e ->
        Ev.tid e = thread ->
        lab G' e = write_label x ty v ->
        valid_execution G' ->

        memory_step G (MWriteFail thread x) G'

  | Step_MMalloc :
      forall G G' e thread x ty,
        valid_execution G ->
        neverAllocated G x ->
        extends_execution G G' e ->
        Ev.tid e = thread ->
        lab G' e = write_label x ty VUndef ->
        valid_execution G' ->

        memory_step G (MMalloc thread x) G'

  | Step_MFree :
      forall G G' e thread x ty,
        valid_execution G ->
        isAllocated G x ->
        extends_execution G G' e ->
        Ev.tid e = thread ->
        lab G' e = write_label x ty VUnalloc ->
        valid_execution G' ->

        memory_step G (MFree thread x) G'.



  Lemma extends_is_w
      G G' e x
      (EXT : extends_execution G G' e)
      (IN : acts_set G x) :
    Ev.is_w (lab G') x = true ->
    Ev.is_w (lab G) x = true.
  Proof.
    intro W.
    unfold Ev.is_w in W.
    rewrite (extends_lab EXT x IN) in W.
    exact W.
  Qed.

  Lemma extends_execution_R: 
    forall G G' e thread x ty v,
      memory_step G (MRead thread x ty v) G' ->
        extends_execution G G' e -> 
        exists e0, 
          acts_set G e0 /\ 
          Ev.is_w (lab G) e0 = true /\ 
          rf G' e0 e.  
  Proof with eauto. 
    intros. 
    inversion H. subst.  
    assert (E_EQ : e = e0). {
      pose proof (extends_G' H6) as E0_IN_G'.
      apply (extends_acts H0 e0) in E0_IN_G'.
      destruct E0_IN_G' as [E0_IN_G | E0_EQ]...  
      exfalso. exact (extends_fresh H6 E0_IN_G).
    } 
    subst e.
    unfold valid_execution in H12.
    destruct H12 as [WF CONS].
    pose proof (consistent_complete M G' CONS) as COMPLETE_G'. 
    unfold complete in COMPLETE_G'.  
    unfold set_inter in COMPLETE_G'. 
    unfold set_subset in COMPLETE_G'. 
    specialize COMPLETE_G' with e0.    
    pose proof (extends_fresh H6) as FRESH.
    pose proof (extends_acts H6 e0) as ACTS.
    assert (acts_set G' e0 /\ Ev.is_r (lab G') e0). {
      split.  
      assert (e0 = e0) by reflexivity. 
      assert (acts_set G e0 \/ e0 = e0). {right...  }
      rewrite <- ACTS in H2... 
      unfold read_label in H10.
      unfold Ev.is_r. rewrite H10...
    } 
    apply COMPLETE_G' in H1.  
    unfold codom_rel in H1. destruct H1 as [x0 RF].      
    pose proof RF as RF_TYPED. 
    apply (wf_rfD WF) in RF_TYPED. 
    unfolder in RF_TYPED. 
    destruct RF_TYPED as [W _].
    pose proof (extends_acts H6 x0) as ACTS_X0.
    assert (X0_IN_G' : acts_set G' x0). {
      pose proof RF as RF_IN_G'.
      apply (wf_rfE WF) in RF_IN_G'.
      unfolder in RF_IN_G'.
      desf.
    }
    assert (X0_NE : x0 <> e0). {
      intro EQ.
      subst x0.
      unfold Ev.is_w in W.
      rewrite H10 in W.
      unfold read_label in W.
      discriminate.
    }
    assert (X0_IN_G : acts_set G x0). {
      apply ACTS_X0 in X0_IN_G'.
      destruct X0_IN_G' as [OLD | NEW]... 
      exfalso. apply X0_NE. exact NEW.
    } 
    pose proof (@extends_is_w G G' e0 x0 H6 X0_IN_G W) as W_OLD.
    exists x0. 
    repeat split...  
  Qed.

  (** TODO: extends_execution_W *)

  End WithModel.

End MemoryModel.
