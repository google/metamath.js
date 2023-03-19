include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cufl.mm"
include "cv.mm"
include "wss.mm"
include "cufil.mm"
include "cfv.mm"
include "wrex.mm"
include "cfil.mm"
include "wral.mm"
include "filssufilg.mm"
include "ancoms.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "pwexr.mm"
include "pwexb.mm"
include "sylibr.mm"
include "isufl.mm"
include "syl.mm"
include "mpbird.mm"

theorem numufl
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vu: setvar u
  let vx: setvar x
  let cY: class Y


  assert |- ( ~P ~P X e. dom card -> X e. UFL )

  proof
    cX
    cpw
    #
    cpw
    ccrd
    cdm
    #
    wcel
    #
    cX
    cufl
    wcel
    #
    vf
    cv
    #
    vg
    cv
    wss
    vg
    cX
    cufil
    cfv
    wrex
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    @2
    @5
    vf
    @6
    @4
    @6
    wcel
    @2
    @5
    vg
    @4
    cX
    filssufilg
    ancoms
    ralrimiva
    @2
    cX
    cvv
    wcel
    #
    @3
    @7
    wb
    @2
    @0
    cvv
    wcel
    @8
    @0
    @1
    pwexr
    cX
    pwexb
    sylibr
    vf
    vg
    cvv
    cX
    isufl
    syl
    mpbird
end
