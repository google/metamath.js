include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "ssun1.mm"
include "eqid.mm"
include "paddval.mm"
include "syl5sseqr.mm"

theorem paddunssN
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cS: class S
  assume padd0.a: |- A = ( Atoms ` K )
  assume padd0.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ X C_ A /\ Y C_ A ) -> ( X u. Y ) C_ ( X .+ Y ) )

  proof
    cK
    cB
    wcel
    cX
    cA
    wss
    cY
    cA
    wss
    w3a
    cX
    cY
    cun
    #
    vp
    cv
    vq
    cv
    vr
    cv
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    vr
    cY
    wrex
    vq
    cX
    wrex
    vp
    cA
    crab
    #
    cun
    @0
    cX
    cY
    c.pl
    co
    @0
    @3
    ssun1
    cA
    cB
    c.pl
    @1
    cK
    @2
    cX
    cY
    vr
    vq
    vp
    @2
    eqid
    @1
    eqid
    padd0.a
    padd0.p
    paddval
    syl5sseqr
end
