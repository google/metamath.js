include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "con3i.mm"

theorem prcnel
  let cA: class A
  let cV: class V


  assert |- ( -. A e. _V -> -. A e. V )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    cA
    cV
    elex
    con3i
end
