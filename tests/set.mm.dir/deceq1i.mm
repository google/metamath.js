include "wceq.mm"
include "cdc.mm"
include "deceq1.mm"
include "ax-mp.mm"

theorem deceq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume deceq1i.1: |- A = B


  assert |- ; A C = ; B C

  proof
    cA
    cB
    wceq
    cA
    cC
    cdc
    cB
    cC
    cdc
    wceq
    deceq1i.1
    cA
    cB
    cC
    deceq1
    ax-mp
end
