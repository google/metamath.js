include "wceq.mm"
include "cdc.mm"
include "deceq2.mm"
include "ax-mp.mm"

theorem deceq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume deceq1i.1: |- A = B


  assert |- ; C A = ; C B

  proof
    cA
    cB
    wceq
    cC
    cA
    cdc
    cC
    cB
    cdc
    wceq
    deceq1i.1
    cA
    cB
    cC
    deceq2
    ax-mp
end
