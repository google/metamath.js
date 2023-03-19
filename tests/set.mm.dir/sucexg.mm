include "wcel.mm"
include "cvv.mm"
include "csuc.mm"
include "elex.mm"
include "sucexb.mm"
include "sylib.mm"

theorem sucexg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> suc A e. _V )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    cA
    csuc
    cvv
    wcel
    cA
    cV
    elex
    cA
    sucexb
    sylib
end
