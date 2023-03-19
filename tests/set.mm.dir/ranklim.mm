include "cvv.mm"
include "wcel.mm"
include "wlim.mm"
include "crnk.mm"
include "cfv.mm"
include "cpw.mm"
include "wb.mm"
include "wa.mm"
include "csuc.mm"
include "limsuc.mm"
include "adantl.mm"
include "cv.mm"
include "wceq.mm"
include "pweq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "suceq.mm"
include "syl.mm"
include "eqeq12d.mm"
include "vex.mm"
include "rankpw.mm"
include "vtoclg.mm"
include "eleq1d.mm"
include "adantr.mm"
include "bitr4d.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "pwexb.mm"
include "sylnbi.mm"
include "eqtr4d.mm"
include "pm2.61ian.mm"

theorem ranklim
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( Lim B -> ( ( rank ` A ) e. B <-> ( rank ` ~P A ) e. B ) )

  proof
    cA
    cvv
    wcel
    #
    cB
    wlim
    #
    cA
    crnk
    cfv
    #
    cB
    wcel
    #
    cA
    cpw
    #
    crnk
    cfv
    #
    cB
    wcel
    #
    wb
    #
    @0
    @1
    wa
    @3
    @2
    csuc
    #
    cB
    wcel
    #
    @6
    @1
    @3
    @9
    wb
    @0
    cB
    @2
    limsuc
    adantl
    @0
    @6
    @9
    wb
    @1
    @0
    @5
    @8
    cB
    vx
    cv
    #
    cpw
    #
    crnk
    cfv
    #
    @10
    crnk
    cfv
    #
    csuc
    #
    wceq
    @5
    @8
    wceq
    vx
    cA
    cvv
    @10
    cA
    wceq
    #
    @12
    @5
    @14
    @8
    @15
    @11
    @4
    crnk
    @10
    cA
    pweq
    fveq2d
    @15
    @13
    @2
    wceq
    @14
    @8
    wceq
    @10
    cA
    crnk
    fveq2
    @13
    @2
    suceq
    syl
    eqeq12d
    @10
    vx
    vex
    rankpw
    vtoclg
    eleq1d
    adantr
    bitr4d
    @0
    wn
    #
    @7
    @1
    @16
    @2
    @5
    cB
    @16
    @2
    c0
    @5
    cA
    crnk
    fvprc
    @0
    @4
    cvv
    wcel
    @5
    c0
    wceq
    cA
    pwexb
    @4
    crnk
    fvprc
    sylnbi
    eqtr4d
    eleq1d
    adantr
    pm2.61ian
end
