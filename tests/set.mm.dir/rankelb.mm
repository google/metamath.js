include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "wa.mm"
include "wn.mm"
include "r1elssi.mm"
include "sseld.mm"
include "rankidn.mm"
include "syl6.mm"
include "imp.mm"
include "wss.mm"
include "wb.mm"
include "rankon.mm"
include "ontri1.mm"
include "mp2an.mm"
include "cdm.mm"
include "wi.mm"
include "rankdmr1.mm"
include "r1ord3g.mm"
include "r1rankidb.mm"
include "sselda.mm"
include "ssel.mm"
include "syl5com.mm"
include "syl5.mm"
include "syl5bir.mm"
include "mt3d.mm"
include "ex.mm"

theorem rankelb
  let cA: class A
  let cB: class B


  assert |- ( B e. U. ( R1 " On ) -> ( A e. B -> ( rank ` A ) e. ( rank ` B ) ) )

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
    wcel
    #
    cA
    crnk
    cfv
    #
    cB
    crnk
    cfv
    #
    wcel
    #
    @1
    @2
    wa
    #
    @5
    cA
    @3
    cr1
    cfv
    #
    wcel
    #
    @1
    @2
    @8
    wn
    #
    @1
    @2
    cA
    @0
    wcel
    @9
    @1
    cB
    @0
    cA
    cB
    r1elssi
    sseld
    cA
    rankidn
    syl6
    imp
    @5
    wn
    #
    @4
    @3
    wss
    #
    @6
    @8
    @4
    con0
    wcel
    @3
    con0
    wcel
    @11
    @10
    wb
    cB
    rankon
    cA
    rankon
    @4
    @3
    ontri1
    mp2an
    @11
    @4
    cr1
    cfv
    #
    @7
    wss
    #
    @6
    @8
    @4
    cr1
    cdm
    #
    wcel
    @3
    @14
    wcel
    @11
    @13
    wi
    cB
    rankdmr1
    cA
    rankdmr1
    @4
    @3
    r1ord3g
    mp2an
    @6
    cA
    @12
    wcel
    @13
    @8
    @1
    cB
    @12
    cA
    cB
    r1rankidb
    sselda
    @12
    @7
    cA
    ssel
    syl5com
    syl5
    syl5bir
    mt3d
    ex
end
