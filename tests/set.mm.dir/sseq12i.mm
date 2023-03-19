include "wceq.mm"
include "wss.mm"
include "wb.mm"
include "sseq12.mm"
include "mp2an.mm"

theorem sseq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume sseq1i.1: |- A = B
  assume sseq12i.2: |- C = D


  assert |- ( A C_ C <-> B C_ D )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    wss
    cB
    cD
    wss
    wb
    sseq1i.1
    sseq12i.2
    cA
    cB
    cC
    cD
    sseq12
    mp2an
end
