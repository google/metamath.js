include "wcel.mm"
include "cima.mm"
include "crn.mm"
include "wss.mm"
include "cvv.mm"
include "imassrn.mm"
include "rnexg.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem imaexg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A " B ) e. _V )

  proof
    cA
    cV
    wcel
    cA
    cB
    cima
    #
    cA
    crn
    #
    wss
    @1
    cvv
    wcel
    @0
    cvv
    wcel
    cA
    cB
    imassrn
    cA
    cV
    rnexg
    @0
    @1
    cvv
    ssexg
    sylancr
end
