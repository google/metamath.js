include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "wb.mm"
include "wa.mm"
include "xrlenlt.mm"
include "con2bid.mm"
include "ancoms.mm"

theorem xrltnle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B <-> -. B <_ A ) )

  proof
    cB
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wn
    wb
    @0
    @1
    wa
    @3
    @2
    cB
    cA
    xrlenlt
    con2bid
    ancoms
end
