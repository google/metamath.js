include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "elpwi.mm"
include "cvv.mm"
include "ssexg.mm"
include "elpwg.mm"
include "biimparc.mm"
include "syldan.mm"
include "expcom.mm"
include "impbid2.mm"

theorem elpw2g
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( A e. ~P B <-> A C_ B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    cpw
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cB
    elpwi
    @2
    @0
    @1
    @2
    @0
    cA
    cvv
    wcel
    #
    @1
    cA
    cB
    cV
    ssexg
    @3
    @1
    @2
    cA
    cB
    cvv
    elpwg
    biimparc
    syldan
    expcom
    impbid2
end
