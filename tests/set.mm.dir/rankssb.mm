include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wss.mm"
include "crnk.mm"
include "cfv.mm"
include "wa.mm"
include "simpr.mm"
include "r1rankidb.mm"
include "adantr.mm"
include "sstrd.mm"
include "cdm.mm"
include "wb.mm"
include "sswf.mm"
include "rankdmr1.mm"
include "rankr1bg.mm"
include "sylancl.mm"
include "mpbid.mm"
include "ex.mm"

theorem rankssb
  let cA: class A
  let cB: class B


  assert |- ( B e. U. ( R1 " On ) -> ( A C_ B -> ( rank ` A ) C_ ( rank ` B ) ) )

  proof
    cB
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    cB
    wss
    #
    cA
    crnk
    cfv
    cB
    crnk
    cfv
    #
    wss
    #
    @1
    @2
    wa
    #
    cA
    @3
    cr1
    cfv
    #
    wss
    #
    @4
    @5
    cA
    cB
    @6
    @1
    @2
    simpr
    @1
    cB
    @6
    wss
    @2
    cB
    r1rankidb
    adantr
    sstrd
    @5
    cA
    @0
    wcel
    @3
    cr1
    cdm
    wcel
    @7
    @4
    wb
    cB
    cA
    sswf
    cB
    rankdmr1
    cA
    @3
    rankr1bg
    sylancl
    mpbid
    ex
end
