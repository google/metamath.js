include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "elprg.mm"
include "ax-mp.mm"

theorem elpr
  let cA: class A
  let cB: class B
  let cC: class C
  assume elpr.1: |- A e. _V


  assert |- ( A e. { B , C } <-> ( A = B \/ A = C ) )

  proof
    cA
    cvv
    wcel
    cA
    cB
    cC
    cpr
    wcel
    cA
    cB
    wceq
    cA
    cC
    wceq
    wo
    wb
    elpr.1
    cA
    cB
    cC
    cvv
    elprg
    ax-mp
end
