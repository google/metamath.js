include "wcel.mm"
include "wfo.mm"
include "wss.mm"
include "w3a.mm"
include "cqtop.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cpw.mm"
include "crab.mm"
include "wa.mm"
include "qtopval2.mm"
include "eleq2d.mm"
include "wceq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "cvv.mm"
include "wb.mm"
include "cuni.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ssexd.mm"
include "simp2.mm"
include "fornex.mm"
include "sylc.mm"
include "elpw2g.mm"
include "syl.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem elqtop
  let cA: class A
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vf: setvar f
  let vj: setvar j
  assume qtopval.1: |- X = U. J


  assert |- ( ( J e. V /\ F : Z -onto-> Y /\ Z C_ X ) -> ( A e. ( J qTop F ) <-> ( A C_ Y /\ ( `' F " A ) e. J ) ) )

  proof
    cJ
    cV
    wcel
    #
    cZ
    cY
    cF
    wfo
    #
    cZ
    cX
    wss
    #
    w3a
    #
    cA
    cJ
    cF
    cqtop
    co
    #
    wcel
    cA
    cF
    ccnv
    #
    vs
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vs
    cY
    cpw
    #
    crab
    #
    wcel
    #
    cA
    cY
    wss
    #
    @5
    cA
    cima
    #
    cJ
    wcel
    #
    wa
    #
    @3
    @4
    @10
    cA
    cF
    cJ
    cV
    cX
    cY
    cZ
    vs
    qtopval.1
    qtopval2
    eleq2d
    @11
    cA
    @9
    wcel
    #
    @14
    wa
    @3
    @15
    @8
    @14
    vs
    cA
    @9
    @6
    cA
    wceq
    @7
    @13
    cJ
    @6
    cA
    @5
    imaeq2
    eleq1d
    elrab
    @3
    @16
    @12
    @14
    @3
    cY
    cvv
    wcel
    #
    @16
    @12
    wb
    @3
    cZ
    cvv
    wcel
    @1
    @17
    @3
    cZ
    cX
    cvv
    @0
    @1
    cX
    cvv
    wcel
    @2
    @0
    cX
    cJ
    cuni
    cvv
    qtopval.1
    cJ
    cV
    uniexg
    syl5eqel
    3ad2ant1
    @0
    @1
    @2
    simp3
    ssexd
    @0
    @1
    @2
    simp2
    cZ
    cY
    cvv
    cF
    fornex
    sylc
    cA
    cY
    cvv
    elpw2g
    syl
    anbi1d
    syl5bb
    bitrd
end
