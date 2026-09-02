From hahn Require Import Hahn.

Require Import Events.
Require Import value.
Require Import memory_model.

Set Implicit Arguments.

Module ThreadMemoryEvents
    (Ev : Events ConcreteValue).

  Inductive thread_mem_event : Type :=
  | TERead :
      Ev.location ->
      Ev.mode ->
      ConcreteValue.t ->
      thread_mem_event
  | TEWrite :
      Ev.location ->
      Ev.mode ->
      ConcreteValue.t ->
      thread_mem_event
  | TEMalloc :
      Ev.location ->
      thread_mem_event
  | TEFree :
      Ev.location ->
      thread_mem_event.

End ThreadMemoryEvents.

Module Type ThreadSemantics
    (Ev : Events ConcreteValue).

  Module Import MemoryEvents := ThreadMemoryEvents Ev.

  Parameter state : Type.
  Parameter genv : Type.
  Parameter external_event : Type.
  Parameter start_info : Type.
  Parameter result : Type.

  Inductive thread_event : Type :=
  | TEExternal :
      external_event ->
      thread_event
  | TEMemory :
      thread_mem_event ->
      thread_event
  | TETau :
      thread_event
  | TEStart :
      Ev.thread_id ->
      start_info ->
      thread_event
  | TEExit :
      thread_event.

  Parameter globalenv :
    genv.

  Parameter step :
    genv ->
    state ->
    thread_event ->
    state ->
    Prop.

  Parameter initial_state :
    state ->
    Prop.

  Parameter start_state :
    start_info ->
    state ->
    Prop.

  Parameter final_state :
    state ->
    result ->
    Prop.

End ThreadSemantics.
