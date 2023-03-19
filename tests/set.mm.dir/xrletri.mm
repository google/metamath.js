include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "clt.mm"
include "wb.mm"
include "xrltnle.mm"
include "ancoms.mm"
include "wi.mm"
include "xrltle.mm"
include "sylbird.mm"
include "orrd.mm"

theorem xrletri
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A <_ B \/ B <_ A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    @2
    @3
    wn
    #
    cB
    cA
    clt
    wbr
    #
    @4
    @1
    @0
    @6
    @5
    wb
    cB
    cA
    xrltnle
    ancoms
    @1
    @0
    @6
    @4
    wi
    cB
    cA
    xrltle
    ancoms
    sylbird
    orrd
end
