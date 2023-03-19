include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wceq.mm"
include "wn.mm"
include "wor.mm"
include "wb.mm"
include "xrltso.mm"
include "sotrieq.mm"
include "mpan.mm"
include "bicomd.mm"
include "necon1abid.mm"

theorem xrlttri2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A =/= B <-> ( A < B \/ B < A ) ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    #
    cA
    cB
    clt
    wbr
    cB
    cA
    clt
    wbr
    wo
    #
    cA
    cB
    @0
    cA
    cB
    wceq
    #
    @1
    wn
    #
    cxr
    clt
    wor
    @0
    @2
    @3
    wb
    xrltso
    cxr
    cA
    cB
    clt
    sotrieq
    mpan
    bicomd
    necon1abid
end
