include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "xrlttri3.mm"
include "ancom.mm"
include "syl6bbr.mm"
include "xrlenlt.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "bitr4d.mm"

theorem xrletri3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A = B <-> ( A <_ B /\ B <_ A ) ) )

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
    wceq
    #
    cB
    cA
    clt
    wbr
    wn
    #
    cA
    cB
    clt
    wbr
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
    cle
    wbr
    #
    wa
    @2
    @3
    @5
    @4
    wa
    @6
    cA
    cB
    xrlttri3
    @4
    @5
    ancom
    syl6bbr
    @2
    @7
    @4
    @8
    @5
    cA
    cB
    xrlenlt
    @1
    @0
    @8
    @5
    wb
    cB
    cA
    xrlenlt
    ancoms
    anbi12d
    bitr4d
end
