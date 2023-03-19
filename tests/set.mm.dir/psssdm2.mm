include "cps.mm"
include "wcel.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "wss.mm"
include "dmin.mm"
include "eqcomi.mm"
include "dmxpid.mm"
include "ineq12i.mm"
include "sseqtri.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "inss1.mm"
include "sseli.mm"
include "psref.mm"
include "sylan2.mm"
include "brinxp2.mm"
include "syl3anbrc.mm"
include "vex.mm"
include "breldm.mm"
include "syl.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem psssdm2
  let cA: class A
  let cR: class R
  let cX: class X
  let vx: setvar x
  assume psssdm.1: |- X = dom R


  assert |- ( R e. PosetRel -> dom ( R i^i ( A X. A ) ) = ( X i^i A ) )

  proof
    cR
    cps
    wcel
    #
    cR
    cA
    cA
    cxp
    #
    cin
    #
    cdm
    #
    cX
    cA
    cin
    #
    @3
    @4
    wss
    @0
    @3
    cR
    cdm
    #
    @1
    cdm
    #
    cin
    @4
    cR
    @1
    dmin
    @5
    cX
    @6
    cA
    cX
    @5
    psssdm.1
    eqcomi
    cA
    dmxpid
    ineq12i
    sseqtri
    a1i
    @0
    vx
    @4
    @3
    @0
    vx
    cv
    #
    @4
    wcel
    #
    @7
    @3
    wcel
    #
    @0
    @8
    wa
    #
    @7
    @7
    @2
    wbr
    #
    @9
    @10
    @7
    cA
    wcel
    #
    @12
    @7
    @7
    cR
    wbr
    #
    @11
    @10
    @4
    cA
    @7
    cX
    cA
    inss2
    @0
    @8
    simpr
    sseldi
    #
    @14
    @8
    @0
    @7
    cX
    wcel
    @13
    @4
    cX
    @7
    cX
    cA
    inss1
    sseli
    @7
    cR
    cX
    psssdm.1
    psref
    sylan2
    @7
    @7
    cA
    cA
    cR
    brinxp2
    syl3anbrc
    @7
    @7
    @2
    vx
    vex
    #
    @15
    breldm
    syl
    ex
    ssrdv
    eqssd
end
