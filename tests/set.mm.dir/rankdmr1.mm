include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cdm.mm"
include "csuc.mm"
include "rankidb.mm"
include "elfvdm.mm"
include "syl.mm"
include "wlim.mm"
include "wb.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "wn.mm"
include "c0.mm"
include "rankvaln.mm"
include "com.mm"
include "wss.mm"
include "limomss.mm"
include "peano1.mm"
include "sselii.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem rankdmr1
  let cA: class A


  assert |- ( rank ` A ) e. dom R1

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    #
    cA
    crnk
    cfv
    #
    cr1
    cdm
    #
    wcel
    #
    @0
    @1
    csuc
    #
    @2
    wcel
    #
    @3
    @0
    cA
    @4
    cr1
    cfv
    wcel
    @5
    cA
    rankidb
    cA
    @4
    cr1
    elfvdm
    syl
    @2
    wlim
    #
    @3
    @5
    wb
    cr1
    wfun
    @6
    r1funlim
    simpri
    #
    @2
    @1
    limsuc
    ax-mp
    sylibr
    @0
    wn
    @1
    c0
    @2
    cA
    rankvaln
    com
    @2
    c0
    @6
    com
    @2
    wss
    @7
    @2
    limomss
    ax-mp
    peano1
    sselii
    syl6eqel
    pm2.61i
end
