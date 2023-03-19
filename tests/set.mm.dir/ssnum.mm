include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "ssdomg.mm"
include "imp.mm"
include "numdom.mm"
include "syldan.mm"

theorem ssnum
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B C_ A ) -> B e. dom card )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cA
    cdom
    wbr
    #
    cB
    @0
    wcel
    @1
    @2
    @3
    cB
    cA
    @0
    ssdomg
    imp
    cA
    cB
    numdom
    syldan
end
