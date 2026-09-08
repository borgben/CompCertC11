From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import value.

Require Import memory_model.
Require Import thread_semantics.

Set Implicit Arguments.


Module Composition (Ev : Events ConcreteValue).

  Module Import MM := MemoryModel Ev.
  Module Import Ex := MM.Ex.

  Module WholeSystem (S : ThreadSemantics Ev).

    Definition thread_pool : Type := Ev.thread_id -> option S.state.

    Parameter thread_id_eq_dec :  forall x y : Ev.thread_id, {x = y} + {x <> y}.

    Definition update_thread (thread : Ev.thread_id) (state : option S.state) (threads : thread_pool) : thread_pool :=
      fun thread' => if thread_id_eq_dec thread' thread then state else threads thread'. 

    Definition add_thread (thread : Ev.thread_id) (state : S.state) (threads : thread_pool) : thread_pool :=
      update_thread thread (Some state) threads.

    Definition remove_thread (thread : Ev.thread_id) (threads : thread_pool) : thread_pool :=
      update_thread thread None threads.


    Record system_state : Type := {
      sys_graph : execution;
      sys_threads : thread_pool
    }.


    Inductive system_event : Type :=
    | WSTau :
        system_event

    | WSExternal :
        S.external_event ->
        system_event

    | WSFail :
        system_event.

    Section WithMemoryModel.

    Context (M : MM.t).


    Inductive system_step : system_state -> system_event -> system_state -> Prop :=
    | Step_Tau : forall G threads thread state state',
          threads thread = Some state -> S.step S.globalenv state S.TETau state' ->
          system_step
            {|
              sys_graph := G;
              sys_threads := threads
            |}
            WSTau
            {|
              sys_graph := G;
              sys_threads := update_thread thread (Some state') threads
            |}
    | Step_External : forall G threads thread state state' event,
          threads thread = Some state -> S.step S.globalenv state (S.TEExternal event) state' ->
              system_step
                {|
                  sys_graph := G;
                  sys_threads := threads
                |}
                (WSExternal event)
                {|
                  sys_graph := G;
                  sys_threads :=
                    update_thread
                      thread
                      (Some state')
                      threads
                |}
    | Step_Read :
        forall G G' threads thread state state' x ord v,
          threads thread = Some state ->
          S.step S.globalenv state (S.TEMemory (S.MemoryEvents.TERead x ord v)) state' ->
          MM.memory_step M G (MM.MRead thread x ord v) G' ->
          system_step
            {| sys_graph := G; sys_threads := threads |}
            WSTau
            {| sys_graph := G';
               sys_threads := update_thread thread (Some state') threads |}

    | Step_ReadFail :
        forall G G' threads thread state state' x ord v,
          threads thread = Some state ->
          S.step S.globalenv state (S.TEMemory (S.MemoryEvents.TERead x ord v)) state' ->
          MM.memory_step M G (MM.MReadFail thread x) G' ->
          system_step
            {| sys_graph := G; sys_threads := threads |}
            WSFail
            {| sys_graph := G';
               sys_threads := update_thread thread (Some state') threads |}

    | Step_Write :
        forall G G' threads thread state state' x ord v,
          threads thread = Some state ->
          S.step S.globalenv state (S.TEMemory (S.MemoryEvents.TEWrite x ord v)) state' ->
          MM.memory_step M G (MM.MWrite thread x ord v) G' ->
          system_step
            {| sys_graph := G; sys_threads := threads |}
            WSTau
            {| sys_graph := G';
               sys_threads := update_thread thread (Some state') threads |}

    | Step_WriteFail :
        forall G G' threads thread state state' x ord v,
          threads thread = Some state ->
          S.step S.globalenv state (S.TEMemory (S.MemoryEvents.TEWrite x ord v)) state' ->
          MM.memory_step M G (MM.MWriteFail thread x) G' ->
          system_step
            {| sys_graph := G; sys_threads := threads |}
            WSFail
            {| sys_graph := G';
               sys_threads := update_thread thread (Some state') threads |}

    | Step_Malloc :
        forall G G' threads thread state state' x,
          threads thread = Some state ->
          S.step S.globalenv state (S.TEMemory (S.MemoryEvents.TEMalloc x)) state' ->
          MM.memory_step M G (MM.MMalloc thread x) G' ->
          system_step
            {| sys_graph := G; sys_threads := threads |}
            WSTau
            {| sys_graph := G';
               sys_threads := update_thread thread (Some state') threads |}

    | Step_Free :
        forall G G' threads thread state state' x,
          threads thread = Some state ->
          S.step S.globalenv state (S.TEMemory (S.MemoryEvents.TEFree x)) state' ->
          MM.memory_step M G (MM.MFree thread x) G' ->
          system_step
            {| sys_graph := G; sys_threads := threads |}
            WSTau
            {| sys_graph := G';
               sys_threads := update_thread thread (Some state') threads |}

    | Step_Start :
        forall G threads thread new_thread state state' new_state info,
          threads thread = Some state ->
          threads new_thread = None ->
          S.step S.globalenv state (S.TEStart new_thread info) state' ->
          S.start_state info new_state ->
          system_step
            {|
              sys_graph := G;
              sys_threads := threads
            |}
            WSTau
            {|
              sys_graph := G;
              sys_threads := add_thread new_thread new_state (update_thread thread (Some state') threads)
            |}
            .

    Parameter main_thread : Ev.thread_id.

    Inductive initial_system_state : system_state -> Prop :=
    | Initial_System_State :
        forall state,
          MM.valid_execution M MM.initial_execution ->
          S.initial_state state ->
          initial_system_state
            {|
              sys_graph := MM.initial_execution;
              sys_threads :=
                fun thread =>
                  if thread_id_eq_dec thread main_thread
                  then Some state
                  else None
            |}.

    Definition final_system_state (system : system_state) (result : S.result) : Prop :=
      exists state, sys_threads system main_thread = Some state /\ S.final_state state result.

    End WithMemoryModel.

  End WholeSystem.

End Composition.
