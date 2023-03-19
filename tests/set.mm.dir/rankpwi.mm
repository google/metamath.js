include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "cpw.mm"
include "wceq.mm"
include "wn.mm"
include "rankidn.mm"
include "rankon.mm"
include "r1suc.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "wss.mm"
include "elpwi.mm"
include "pwidg.mm"
include "ssel.mm"
include "syl2imc.mm"
include "syl5bi.mm"
include "mtod.mm"
include "r1rankidb.mm"
include "sspwb.mm"
include "sylib.mm"
include "syl6sseqr.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "onsuci.mm"
include "syl6eleqr.mm"
include "wa.mm"
include "wb.mm"
include "pwwf.mm"
include "rankr1c.mm"
include "sylbi.mm"
include "mpbir2and.mm"
include "eqcomd.mm"

theorem rankpwi
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) -> ( rank ` ~P A ) = suc ( rank ` A ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    crnk
    cfv
    #
    csuc
    #
    cA
    cpw
    #
    crnk
    cfv
    #
    @1
    @3
    @5
    wceq
    #
    @4
    @3
    cr1
    cfv
    #
    wcel
    #
    wn
    #
    @4
    @3
    csuc
    cr1
    cfv
    #
    wcel
    #
    @1
    @8
    cA
    @2
    cr1
    cfv
    #
    wcel
    #
    cA
    rankidn
    @8
    @4
    @12
    cpw
    #
    wcel
    #
    @1
    @13
    @7
    @14
    @4
    @2
    con0
    wcel
    @7
    @14
    wceq
    cA
    rankon
    #
    @2
    r1suc
    ax-mp
    #
    eleq2i
    @15
    @4
    @12
    wss
    @1
    cA
    @4
    wcel
    @13
    @4
    @12
    elpwi
    cA
    @0
    pwidg
    @4
    @12
    cA
    ssel
    syl2imc
    syl5bi
    mtod
    @1
    @4
    @7
    cpw
    #
    @10
    @1
    @4
    @7
    wss
    @4
    @18
    wcel
    @1
    @4
    @14
    @7
    @1
    cA
    @12
    wss
    @4
    @14
    wss
    cA
    r1rankidb
    cA
    @12
    sspwb
    sylib
    @17
    syl6sseqr
    @4
    @7
    @3
    cr1
    fvex
    elpw2
    sylibr
    @3
    con0
    wcel
    @10
    @18
    wceq
    @2
    @16
    onsuci
    @3
    r1suc
    ax-mp
    syl6eleqr
    @1
    @4
    @0
    wcel
    @6
    @9
    @11
    wa
    wb
    cA
    pwwf
    @4
    @3
    rankr1c
    sylbi
    mpbir2and
    eqcomd
end
