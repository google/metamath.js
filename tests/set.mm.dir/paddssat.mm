include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "eqid.mm"
include "paddval.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "ssrab2.mm"
include "jctir.mm"
include "sylib.mm"
include "3adant1.mm"
include "eqsstrd.mm"

theorem paddssat
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


  assert |- ( ( K e. B /\ X C_ A /\ Y C_ A ) -> ( X .+ Y ) C_ A )

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
    cX
    cY
    c.pl
    co
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
    #
    vp
    cA
    crab
    #
    cun
    #
    cA
    cA
    cB
    c.pl
    @4
    cK
    @5
    cX
    cY
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
    @1
    @2
    @8
    cA
    wss
    #
    @0
    @1
    @2
    wa
    #
    @3
    cA
    wss
    #
    @7
    cA
    wss
    #
    wa
    @9
    @10
    @11
    @12
    @10
    @11
    cX
    cY
    cA
    unss
    biimpi
    @6
    vp
    cA
    ssrab2
    jctir
    @3
    @7
    cA
    unss
    sylib
    3adant1
    eqsstrd
end
