include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wral.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "numthcor.mm"
include "onintrab2.mm"
include "sylib.mm"
include "cdom.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "onelon.mm"
include "ex.mm"
include "syl.mm"
include "breq2.mm"
include "onnminsb.mm"
include "syli.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "domtri.mm"
include "mpan.mm"
include "sylibrd.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfbr.mm"
include "onminsb.mm"
include "jctird.mm"
include "domsdomtr.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "iscard.mm"
include "sylanbrc.mm"

theorem cardmin
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint V y
  assert |- ( A e. V -> ( card ` |^| { x e. On | A ~< x } ) = |^| { x e. On | A ~< x } )

  proof
    cA
    cV
    wcel
    #
    cA
    vx
    cv
    #
    csdm
    wbr
    #
    vx
    con0
    crab
    #
    cint
    #
    con0
    wcel
    #
    vy
    cv
    #
    @4
    csdm
    wbr
    #
    vy
    @4
    wral
    @4
    ccrd
    cfv
    @4
    wceq
    @0
    @2
    vx
    con0
    wrex
    #
    @5
    vx
    cA
    cV
    numthcor
    #
    @2
    vx
    onintrab2
    sylib
    #
    @0
    @7
    vy
    @4
    @0
    @6
    @4
    wcel
    #
    @6
    cA
    cdom
    wbr
    #
    cA
    @4
    csdm
    wbr
    #
    wa
    @7
    @0
    @11
    @12
    @13
    @0
    @11
    cA
    @6
    csdm
    wbr
    #
    wn
    #
    @12
    @11
    @0
    @6
    con0
    wcel
    #
    @15
    @0
    @5
    @11
    @16
    wi
    @10
    @5
    @11
    @16
    @4
    @6
    onelon
    ex
    syl
    @2
    @14
    vx
    @6
    @1
    @6
    cA
    csdm
    breq2
    onnminsb
    syli
    @6
    cvv
    wcel
    @0
    @12
    @15
    wb
    vy
    vex
    @6
    cA
    cvv
    cV
    domtri
    mpan
    sylibrd
    @0
    @8
    @13
    @9
    @2
    @13
    vx
    vx
    cA
    @4
    csdm
    vx
    cA
    nfcv
    vx
    csdm
    nfcv
    vx
    @3
    @2
    vx
    con0
    nfrab1
    nfint
    nfbr
    @1
    @4
    cA
    csdm
    breq2
    onminsb
    syl
    jctird
    @6
    cA
    @4
    domsdomtr
    syl6
    ralrimiv
    vy
    @4
    iscard
    sylanbrc
end
