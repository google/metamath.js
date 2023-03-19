include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "cle.mm"
include "wne.mm"
include "wo.mm"
include "xrlttri.mm"
include "ioran.mm"
include "ancom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "xrlenlt.mm"
include "wb.mm"
include "nesym.mm"
include "a1i.mm"
include "anbi12d.mm"
include "bitr4d.mm"

theorem xrltlen
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B <-> ( A <_ B /\ B =/= A ) ) )

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
    #
    cB
    cA
    clt
    wbr
    #
    wn
    #
    cA
    cB
    wceq
    #
    wn
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
    wne
    #
    wa
    @0
    @1
    @4
    @2
    wo
    wn
    #
    @6
    cA
    cB
    xrlttri
    @9
    @5
    @3
    wa
    @6
    @4
    @2
    ioran
    @5
    @3
    ancom
    bitri
    syl6bb
    @0
    @7
    @3
    @8
    @5
    cA
    cB
    xrlenlt
    @8
    @5
    wb
    @0
    cB
    cA
    nesym
    a1i
    anbi12d
    bitr4d
end
