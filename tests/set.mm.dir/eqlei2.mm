include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "wa.mm"
include "eqcom.mm"
include "wb.mm"
include "letri3.mm"
include "mpan.mm"
include "syl5bb.mm"
include "simpr.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem eqlei2
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR


  assert |- ( B = A -> B <_ A )

  proof
    cB
    cr
    wcel
    #
    cB
    cA
    wceq
    #
    cB
    cA
    cle
    wbr
    #
    cA
    cr
    wcel
    #
    @1
    @0
    wi
    lt.1
    cA
    cr
    cB
    eleq1a
    ax-mp
    @0
    @1
    cA
    cB
    cle
    wbr
    #
    @2
    wa
    #
    @2
    @1
    cA
    cB
    wceq
    #
    @0
    @5
    cB
    cA
    eqcom
    @3
    @0
    @6
    @5
    wb
    lt.1
    cA
    cB
    letri3
    mpan
    syl5bb
    @4
    @2
    simpr
    syl6bi
    mpcom
end
