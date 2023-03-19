include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "csn.mm"
include "wral.mm"
include "crab.mm"
include "cint.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "ralsng.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "snwf.mm"
include "rankval3b.mm"
include "syl.mm"
include "rankon.mm"
include "onsucmin.mm"
include "mp1i.mm"
include "3eqtr4d.mm"

theorem ranksnb
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. U. ( R1 " On ) -> ( rank ` { A } ) = suc ( rank ` A ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    vy
    cv
    #
    crnk
    cfv
    #
    vx
    cv
    #
    wcel
    #
    vy
    cA
    csn
    #
    wral
    #
    vx
    con0
    crab
    #
    cint
    #
    cA
    crnk
    cfv
    #
    @4
    wcel
    #
    vx
    con0
    crab
    #
    cint
    #
    @6
    crnk
    cfv
    #
    @10
    csuc
    #
    @1
    @8
    @12
    @1
    @7
    @11
    vx
    con0
    @5
    @11
    vy
    cA
    @0
    @2
    cA
    wceq
    @3
    @10
    @4
    @2
    cA
    crnk
    fveq2
    eleq1d
    ralsng
    rabbidv
    inteqd
    @1
    @6
    @0
    wcel
    @14
    @9
    wceq
    cA
    snwf
    vx
    vy
    @6
    rankval3b
    syl
    @10
    con0
    wcel
    @15
    @13
    wceq
    @1
    cA
    rankon
    vx
    @10
    onsucmin
    mp1i
    3eqtr4d
end
