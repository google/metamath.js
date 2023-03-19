include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "ssid.mm"
include "cdm.mm"
include "wb.mm"
include "rankdmr1.mm"
include "rankr1bg.mm"
include "mpan2.mm"
include "mpbiri.mm"

theorem r1rankidb
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) -> A C_ ( R1 ` ( rank ` A ) ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    #
    cA
    cA
    crnk
    cfv
    #
    cr1
    cfv
    wss
    #
    @1
    @1
    wss
    #
    @1
    ssid
    @0
    @1
    cr1
    cdm
    wcel
    @2
    @3
    wb
    cA
    rankdmr1
    cA
    @1
    rankr1bg
    mpan2
    mpbiri
end
