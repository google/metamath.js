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
include "ssun2.mm"
include "ssun1.mm"
include "sstri.mm"
include "wceq.mm"
include "eqid.mm"
include "paddval.mm"
include "3com23.mm"
include "syl5sseqr.mm"

theorem sspadd2
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


  assert |- ( ( K e. B /\ X C_ A /\ Y C_ A ) -> X C_ ( Y .+ X ) )

  proof
    cK
    cB
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    cY
    cX
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
    cX
    wrex
    vq
    cY
    wrex
    vp
    cA
    crab
    #
    cun
    #
    cX
    cY
    cX
    c.pl
    co
    #
    cX
    @3
    @7
    cX
    cY
    ssun2
    @3
    @6
    ssun1
    sstri
    @0
    @2
    @1
    @8
    @7
    wceq
    cA
    cB
    c.pl
    @4
    cK
    @5
    cY
    cX
    vr
    vq
    vp
    @5
    eqid
    @4
    eqid
    padd0.a
    padd0.p
    paddval
    3com23
    syl5sseqr
end
