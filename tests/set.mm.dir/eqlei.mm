include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "eqcoms.mm"
include "wa.mm"
include "wb.mm"
include "letri3.mm"
include "mpan.mm"
include "simpl.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem eqlei
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR


  assert |- ( A = B -> A <_ B )

  proof
    cB
    cr
    wcel
    #
    cA
    cB
    wceq
    #
    cA
    cB
    cle
    wbr
    #
    @0
    cB
    cA
    cA
    cr
    wcel
    #
    cB
    cA
    wceq
    @0
    wi
    lt.1
    cA
    cr
    cB
    eleq1a
    ax-mp
    eqcoms
    @0
    @1
    @2
    cB
    cA
    cle
    wbr
    #
    wa
    #
    @2
    @3
    @0
    @1
    @5
    wb
    lt.1
    cA
    cB
    letri3
    mpan
    @2
    @4
    simpl
    syl6bi
    mpcom
end
