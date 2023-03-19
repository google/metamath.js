include "eqcomi.mm"
include "sseqtri.mm"

theorem sseqtr4i
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseqtr4.1: |- A C_ B
  assume sseqtr4.2: |- C = B


  assert |- A C_ C

  proof
    cA
    cB
    cC
    sseqtr4.1
    cC
    cB
    sseqtr4.2
    eqcomi
    sseqtri
end
