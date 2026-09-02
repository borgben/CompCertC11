value.vo value.glob value.v.beautified value.required_vo: value.v 
value.vio: value.v 
value.vos value.vok value.required_vos: value.v 
memory_model.vo memory_model.glob memory_model.v.beautified memory_model.required_vo: memory_model.v imm/src/basic/Events.vo imm/src/basic/Execution.vo value.vo
memory_model.vio: memory_model.v imm/src/basic/Events.vio imm/src/basic/Execution.vio value.vio
memory_model.vos memory_model.vok memory_model.required_vos: memory_model.v imm/src/basic/Events.vos imm/src/basic/Execution.vos value.vos
thread_semantics.vo thread_semantics.glob thread_semantics.v.beautified thread_semantics.required_vo: thread_semantics.v imm/src/basic/Events.vo value.vo memory_model.vo
thread_semantics.vio: thread_semantics.v imm/src/basic/Events.vio value.vio memory_model.vio
thread_semantics.vos thread_semantics.vok thread_semantics.required_vos: thread_semantics.v imm/src/basic/Events.vos value.vos memory_model.vos
mem_comp.vo mem_comp.glob mem_comp.v.beautified mem_comp.required_vo: mem_comp.v imm/src/basic/Events.vo imm/src/basic/Execution.vo value.vo memory_model.vo thread_semantics.vo
mem_comp.vio: mem_comp.v imm/src/basic/Events.vio imm/src/basic/Execution.vio value.vio memory_model.vio thread_semantics.vio
mem_comp.vos mem_comp.vok mem_comp.required_vos: mem_comp.v imm/src/basic/Events.vos imm/src/basic/Execution.vos value.vos memory_model.vos thread_semantics.vos
