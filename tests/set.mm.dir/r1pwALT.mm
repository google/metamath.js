include "cvv.mm"
include "wcel.mm"
include "con0.mm"
include "cr1.mm"
include "cfv.mm"
include "cpw.mm"
include "csuc.mm"
include "wb.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "pweq.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "crnk.mm"
include "vex.mm"
include "rankr1a.mm"
include "word.mm"
include "eloni.mm"
include "ordsucelsuc.mm"
include "syl.mm"
include "bitrd.mm"
include "rankpw.mm"
include "eleq1i.mm"
include "syl6bbr.mm"
include "suceloni.mm"
include "pwex.mm"
include "bitr4d.mm"
include "vtoclg.mm"
include "wn.mm"
include "elex.mm"
include "pwexb.mm"
include "sylibr.mm"
include "pm5.21ni.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem r1pwALT
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( B e. On -> ( A e. ( R1 ` B ) <-> ~P A e. ( R1 ` suc B ) ) )

  proof
    cA
    cvv
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cB
    cr1
    cfv
    #
    wcel
    #
    cA
    cpw
    #
    cB
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    wb
    #
    wi
    #
    @1
    vx
    cv
    #
    @2
    wcel
    #
    @10
    cpw
    #
    @6
    wcel
    #
    wb
    #
    wi
    @9
    vx
    cA
    cvv
    @10
    cA
    wceq
    #
    @14
    @8
    @1
    @15
    @11
    @3
    @13
    @7
    @10
    cA
    @2
    eleq1
    @15
    @12
    @4
    @6
    @10
    cA
    pweq
    eleq1d
    bibi12d
    imbi2d
    @1
    @11
    @12
    crnk
    cfv
    #
    @5
    wcel
    #
    @13
    @1
    @11
    @10
    crnk
    cfv
    #
    csuc
    #
    @5
    wcel
    #
    @17
    @1
    @11
    @18
    cB
    wcel
    #
    @20
    @10
    cB
    vx
    vex
    #
    rankr1a
    @1
    cB
    word
    @21
    @20
    wb
    cB
    eloni
    @18
    cB
    ordsucelsuc
    syl
    bitrd
    @16
    @19
    @5
    @10
    @22
    rankpw
    eleq1i
    syl6bbr
    @1
    @5
    con0
    wcel
    @13
    @17
    wb
    cB
    suceloni
    @12
    @5
    @10
    @22
    pwex
    rankr1a
    syl
    bitr4d
    vtoclg
    @0
    wn
    @8
    @1
    @3
    @0
    @7
    cA
    @2
    elex
    @7
    @4
    cvv
    wcel
    @0
    @4
    @6
    elex
    cA
    pwexb
    sylibr
    pm5.21ni
    a1d
    pm2.61i
end
