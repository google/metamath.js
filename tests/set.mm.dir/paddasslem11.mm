include "chlt.mm"
include "wcel.mm"
include "weq.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "simplll.mm"
include "simplr3.mm"
include "simplr1.mm"
include "simplr2.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "sspadd2.mm"
include "simpllr.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "sseldd.mm"

theorem paddasslem11
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vs: setvar s
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( ( K e. HL /\ p = z ) /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) ) /\ z e. Z ) -> p e. ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    vp
    vz
    weq
    #
    wa
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    cZ
    cA
    wss
    #
    w3a
    #
    wa
    #
    vz
    cv
    #
    cZ
    wcel
    #
    wa
    #
    cZ
    cX
    cY
    c.pl
    co
    #
    cZ
    c.pl
    co
    #
    vp
    cv
    #
    @10
    @0
    @5
    @11
    cA
    wss
    #
    cZ
    @12
    wss
    @0
    @1
    @6
    @9
    simplll
    #
    @3
    @4
    @5
    @2
    @9
    simplr3
    @10
    @0
    @3
    @4
    @14
    @15
    @3
    @4
    @5
    @2
    @9
    simplr1
    @3
    @4
    @5
    @2
    @9
    simplr2
    cA
    chlt
    c.pl
    cK
    cX
    cY
    paddasslem.a
    paddasslem.p
    paddssat
    syl3anc
    cA
    chlt
    c.pl
    cK
    cZ
    @11
    paddasslem.a
    paddasslem.p
    sspadd2
    syl3anc
    @10
    @13
    @8
    cZ
    @0
    @1
    @6
    @9
    simpllr
    @7
    @9
    simpr
    eqeltrd
    sseldd
end
