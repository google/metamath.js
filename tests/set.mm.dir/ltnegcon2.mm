include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "renegcl.mm"
include "ltneg.mm"
include "sylan2.mm"
include "simpr.mm"
include "recnd.mm"
include "negnegd.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem ltnegcon2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < -u B <-> B < -u A ) )

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
    cneg
    #
    clt
    wbr
    #
    @3
    cneg
    #
    cA
    cneg
    #
    clt
    wbr
    #
    cB
    @6
    clt
    wbr
    @1
    @0
    @3
    cr
    wcel
    @4
    @7
    wb
    cB
    renegcl
    cA
    @3
    ltneg
    sylan2
    @2
    @5
    cB
    @6
    clt
    @2
    cB
    @2
    cB
    @0
    @1
    simpr
    recnd
    negnegd
    breq1d
    bitrd
end
