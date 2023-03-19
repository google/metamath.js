include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "wss.mm"
include "r1rankidb.mm"
include "sspwb.mm"
include "sylib.mm"
include "cdm.mm"
include "wceq.mm"
include "rankdmr1.mm"
include "r1sucg.mm"
include "ax-mp.mm"
include "syl6sseqr.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "wlim.mm"
include "wb.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limsuc.mm"
include "mpbi.mm"
include "syl6eleqr.mm"
include "r1elwf.mm"
include "syl.mm"
include "r1elssi.mm"
include "cvv.mm"
include "pwexr.mm"
include "pwidg.mm"
include "sseldd.mm"
include "impbii.mm"

theorem pwwf
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) <-> ~P A e. U. ( R1 " On ) )

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
    cpw
    #
    @0
    wcel
    #
    @1
    @2
    cA
    crnk
    cfv
    #
    csuc
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    @3
    @1
    @2
    @5
    cr1
    cfv
    #
    cpw
    #
    @7
    @1
    @2
    @8
    wss
    @2
    @9
    wcel
    @1
    @2
    @4
    cr1
    cfv
    #
    cpw
    #
    @8
    @1
    cA
    @10
    wss
    @2
    @11
    wss
    cA
    r1rankidb
    cA
    @10
    sspwb
    sylib
    @4
    cr1
    cdm
    #
    wcel
    #
    @8
    @11
    wceq
    cA
    rankdmr1
    #
    @4
    r1sucg
    ax-mp
    syl6sseqr
    @2
    @8
    @5
    cr1
    fvex
    elpw2
    sylibr
    @5
    @12
    wcel
    #
    @7
    @9
    wceq
    @13
    @15
    @14
    @12
    wlim
    #
    @13
    @15
    wb
    cr1
    wfun
    @16
    r1funlim
    simpri
    @12
    @4
    limsuc
    ax-mp
    mpbi
    @5
    r1sucg
    ax-mp
    syl6eleqr
    @2
    @6
    r1elwf
    syl
    @3
    @2
    @0
    cA
    @2
    r1elssi
    @3
    cA
    cvv
    wcel
    cA
    @2
    wcel
    cA
    @0
    pwexr
    cA
    cvv
    pwidg
    syl
    sseldd
    impbii
end
