include "wcel.mm"
include "cvv.mm"
include "cqtop.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "wa.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cin.mm"
include "cpw.mm"
include "crab.mm"
include "resima.mm"
include "pweqi.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "residm.mm"
include "cnveqi.mm"
include "imaeq1i.mm"
include "cnvresima.mm"
include "3eqtr3i.mm"
include "eleq1i.mm"
include "rabbii.mm"
include "eqtr2i.mm"
include "qtopval.mm"
include "resexg.mm"
include "sylan2.mm"
include "3eqtr4a.mm"
include "expcom.mm"
include "wn.mm"
include "c0.mm"
include "cuni.mm"
include "df-qtop.mm"
include "reldmmpt2.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "pm2.61d1.mm"

theorem qtopres
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let cA: class A
  let vs: setvar s
  let vf: setvar f
  let vj: setvar j
  let cY: class Y
  let cZ: class Z
  assume qtopval.1: |- X = U. J


  assert |- ( F e. V -> ( J qTop F ) = ( J qTop ( F |` X ) ) )

  proof
    cF
    cV
    wcel
    #
    cJ
    cvv
    wcel
    #
    cJ
    cF
    cqtop
    co
    #
    cJ
    cF
    cX
    cres
    #
    cqtop
    co
    #
    wceq
    #
    @1
    @0
    @5
    @1
    @0
    wa
    cF
    ccnv
    vs
    cv
    #
    cima
    cX
    cin
    #
    cJ
    wcel
    #
    vs
    cF
    cX
    cima
    #
    cpw
    #
    crab
    #
    @3
    ccnv
    #
    @6
    cima
    #
    cX
    cin
    #
    cJ
    wcel
    #
    vs
    @3
    cX
    cima
    #
    cpw
    #
    crab
    #
    @2
    @4
    @18
    @15
    vs
    @10
    crab
    #
    @11
    @17
    @10
    wceq
    @18
    @19
    wceq
    @16
    @9
    cF
    cX
    resima
    pweqi
    @15
    vs
    @17
    @10
    rabeq
    ax-mp
    @15
    @8
    vs
    @10
    @14
    @7
    cJ
    @3
    cX
    cres
    #
    ccnv
    #
    @6
    cima
    @13
    @14
    @7
    @21
    @12
    @6
    @20
    @3
    cF
    cX
    residm
    cnveqi
    imaeq1i
    cX
    @6
    @3
    cnvresima
    cX
    @6
    cF
    cnvresima
    3eqtr3i
    eleq1i
    rabbii
    eqtr2i
    cF
    cJ
    cvv
    cV
    cX
    vs
    qtopval.1
    qtopval
    @0
    @1
    @3
    cvv
    wcel
    @4
    @18
    wceq
    cF
    cX
    cV
    resexg
    @3
    cJ
    cvv
    cvv
    cX
    vs
    qtopval.1
    qtopval
    sylan2
    3eqtr4a
    expcom
    @1
    wn
    @2
    c0
    @4
    cJ
    cF
    cqtop
    vj
    vf
    cvv
    cvv
    vf
    cv
    #
    ccnv
    @6
    cima
    vj
    cv
    #
    cuni
    #
    cin
    @23
    wcel
    vs
    @22
    @24
    cima
    cpw
    crab
    cqtop
    vf
    vj
    vs
    df-qtop
    reldmmpt2
    #
    ovprc1
    cJ
    @3
    cqtop
    @25
    ovprc1
    eqtr4d
    pm2.61d1
end
