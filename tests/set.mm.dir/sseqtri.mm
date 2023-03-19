include "wss.mm"
include "sseq2i.mm"
include "mpbi.mm"

theorem sseqtri
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseqtr.1: |- A C_ B
  assume sseqtr.2: |- B = C


  assert |- A C_ C

  proof
    cA
    cB
    wss
    cA
    cC
    wss
    sseqtr.1
    cB
    cC
    cA
    sseqtr.2
    sseq2i
    mpbi
end
