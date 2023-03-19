include "cres.mm"
include "wss.mm"
include "wcel.mm"
include "cvv.mm"
include "resss.mm"
include "ssexg.mm"
include "mpan.mm"

theorem resexg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A |` B ) e. _V )

  proof
    cA
    cB
    cres
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
    resss
    @0
    cA
    cV
    ssexg
    mpan
end
