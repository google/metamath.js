include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "lenlt.mm"
include "eqcom.mm"
include "orbi1i.mm"
include "orcom.mm"
include "bitri.mm"
include "wb.mm"
include "axlttri.mm"
include "ancoms.mm"
include "con2bid.mm"
include "syl5rbbr.mm"
include "bitrd.mm"

theorem leloe
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B <-> ( A < B \/ A = B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    cB
    cA
    clt
    wbr
    #
    wn
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    wceq
    #
    wo
    #
    cA
    cB
    lenlt
    @7
    cB
    cA
    wceq
    #
    @5
    wo
    #
    @2
    @4
    @9
    @6
    @5
    wo
    @7
    @8
    @6
    @5
    cB
    cA
    eqcom
    orbi1i
    @6
    @5
    orcom
    bitri
    @2
    @3
    @9
    @1
    @0
    @3
    @9
    wn
    wb
    cB
    cA
    axlttri
    ancoms
    con2bid
    syl5rbbr
    bitrd
end
