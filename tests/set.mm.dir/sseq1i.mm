include "wceq.mm"
include "wss.mm"
include "wb.mm"
include "sseq1.mm"
include "ax-mp.mm"

theorem sseq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseq1i.1: |- A = B


  assert |- ( A C_ C <-> B C_ C )

  proof
    cA
    cB
    wceq
    cA
    cC
    wss
    cB
    cC
    wss
    wb
    sseq1i.1
    cA
    cB
    cC
    sseq1
    ax-mp
end
