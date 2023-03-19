include "wor.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wa.mm"
include "df-so.mm"
include "nfpo.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "nf3or.mm"
include "nfral.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nfso
  let vx: setvar x
  let cA: class A
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume nfpo.r: |- F/_ x R
  assume nfpo.a: |- F/_ x A


  assert |- F/ x R Or A

  proof
    cA
    cR
    wor
    cA
    cR
    wpo
    #
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
    vb
    weq
    #
    @2
    @1
    cR
    wbr
    #
    w3o
    #
    vb
    cA
    wral
    #
    va
    cA
    wral
    #
    wa
    vx
    va
    vb
    cA
    cR
    df-so
    @0
    @8
    vx
    vx
    cA
    cR
    nfpo.r
    nfpo.a
    nfpo
    @7
    vx
    va
    cA
    nfpo.a
    @6
    vx
    vb
    cA
    nfpo.a
    @3
    @4
    @5
    vx
    vx
    @1
    @2
    cR
    vx
    @1
    nfcv
    #
    nfpo.r
    vx
    @2
    nfcv
    #
    nfbr
    @4
    vx
    nfv
    vx
    @2
    @1
    cR
    @10
    nfpo.r
    @9
    nfbr
    nf3or
    nfral
    nfral
    nfan
    nfxfr
end
