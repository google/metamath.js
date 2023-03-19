include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "df-po.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfn.mm"
include "nfan.mm"
include "nfim.mm"
include "nfral.mm"
include "nfxfr.mm"

theorem nfpo
  let vx: setvar x
  let cA: class A
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume nfpo.r: |- F/_ x R
  assume nfpo.a: |- F/_ x A


  assert |- F/ x R Po A

  proof
    cA
    cR
    wpo
    va
    cv
    #
    @0
    cR
    wbr
    #
    wn
    #
    @0
    vb
    cv
    #
    cR
    wbr
    #
    @3
    vc
    cv
    #
    cR
    wbr
    #
    wa
    #
    @0
    @5
    cR
    wbr
    #
    wi
    #
    wa
    #
    vc
    cA
    wral
    #
    vb
    cA
    wral
    #
    va
    cA
    wral
    vx
    va
    vb
    vc
    cA
    cR
    df-po
    @12
    vx
    va
    cA
    nfpo.a
    @11
    vx
    vb
    cA
    nfpo.a
    @10
    vx
    vc
    cA
    nfpo.a
    @2
    @9
    vx
    @1
    vx
    vx
    @0
    @0
    cR
    vx
    @0
    nfcv
    #
    nfpo.r
    @13
    nfbr
    nfn
    @7
    @8
    vx
    @4
    @6
    vx
    vx
    @0
    @3
    cR
    @13
    nfpo.r
    vx
    @3
    nfcv
    #
    nfbr
    vx
    @3
    @5
    cR
    @14
    nfpo.r
    vx
    @5
    nfcv
    #
    nfbr
    nfan
    vx
    @0
    @5
    cR
    @13
    nfpo.r
    @15
    nfbr
    nfim
    nfan
    nfral
    nfral
    nfral
    nfxfr
end
