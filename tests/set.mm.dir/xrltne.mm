include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wne.mm"
include "wo.mm"
include "wa.mm"
include "orc.mm"
include "wor.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "xrltso.mm"
include "sotrieq.mm"
include "mpan.mm"
include "necon2abid.mm"
include "syl5ib.mm"
include "3impia.mm"
include "necomd.mm"

theorem xrltne
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> B =/= A )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    cA
    cB
    @0
    @1
    @2
    cA
    cB
    wne
    #
    @2
    @2
    cB
    cA
    clt
    wbr
    #
    wo
    #
    @0
    @1
    wa
    #
    @3
    @2
    @4
    orc
    @6
    @5
    cA
    cB
    cxr
    clt
    wor
    @6
    cA
    cB
    wceq
    @5
    wn
    wb
    xrltso
    cxr
    cA
    cB
    clt
    sotrieq
    mpan
    necon2abid
    syl5ib
    3impia
    necomd
end
