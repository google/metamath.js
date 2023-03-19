include "cdif.mm"
include "wss.mm"
include "wcel.mm"
include "cvv.mm"
include "difss.mm"
include "ssexg.mm"
include "mpan.mm"

theorem difexg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A \ B ) e. _V )

  proof
    cA
    cB
    cdif
    #
    cA
    wss
    cA
    cV
    wcel
    @0
    cvv
    wcel
    cA
    cB
    difss
    @0
    cA
    cV
    ssexg
    mpan
end
