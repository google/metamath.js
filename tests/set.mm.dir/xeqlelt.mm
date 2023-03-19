include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "xrletri3.mm"
include "wb.mm"
include "xrlenlt.mm"
include "ancoms.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem xeqlelt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A = B <-> ( A <_ B /\ -. A < B ) ) )

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
    @3
    cA
    cB
    clt
    wbr
    wn
    #
    wa
    cA
    cB
    xrletri3
    @2
    @4
    @5
    @3
    @1
    @0
    @4
    @5
    wb
    cB
    cA
    xrlenlt
    ancoms
    anbi2d
    bitrd
end
