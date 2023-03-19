include "wss.mm"
include "sseq1i.mm"
include "mpbir.mm"

theorem eqsstri
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqsstr.1: |- A = B
  assume eqsstr.2: |- B C_ C


  assert |- A C_ C

  proof
    cA
    cC
    wss
    cB
    cC
    wss
    eqsstr.2
    cA
    cB
    cC
    eqsstr.1
    sseq1i
    mpbir
end
