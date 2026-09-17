import ClAsm.Codegen.Emit
import ClAsm.Layout

namespace ClAsm.Codegen

def linkerScript (name : String) : String :=
  s!"OUTPUT_ARCH(riscv)\nENTRY({symbolName name})\n" ++
  "PHDRS { text PT_LOAD FLAGS(5); }\n" ++
  "SECTIONS { . = " ++ toString ClAsm.Layout.entry ++ "; .text : { *(.text) } :text }\n"

end ClAsm.Codegen
