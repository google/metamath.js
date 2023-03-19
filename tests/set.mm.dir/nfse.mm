include "wse.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "df-se.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfrab.mm"
include "nfel1.mm"
include "nfral.mm"
include "nfxfr.mm"

theorem nfse
  let vx: setvar x
  let cA: class A
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume nffr.r: |- F/_ x R
  assume nffr.a: |- F/_ x A


  assert |- F/ x R Se A

  proof
    cA
    cR
    wse
    va
    cv
    #
    vb
    cv
    #
    cR
    wbr
    #
    va
    cA
    crab
    #
    cvv
    wcel
    #
    vb
    cA
    wral
    vx
    vb
    va
    cA
    cR
    df-se
    @4
    vx
    vb
    cA
    nffr.a
    vx
    @3
    cvv
    @2
    vx
    va
    cA
    vx
    @0
    @1
    cR
    vx
    @0
    nfcv
    nffr.r
    vx
    @1
    nfcv
    nfbr
    nffr.a
    nfrab
    nfel1
    nfral
    nfxfr
end
