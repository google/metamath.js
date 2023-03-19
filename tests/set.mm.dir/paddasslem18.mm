include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "co.mm"
include "cjn.mm"
include "cfv.mm"
include "cple.mm"
include "eqid.mm"
include "paddasslem16.mm"
include "3expa.mm"
include "wn.mm"
include "paddasslem17.mm"
include "pm2.61dan.mm"

theorem paddasslem18
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume paddass.a: |- A = ( Atoms ` K )
  assume paddass.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) ) -> ( X .+ ( Y .+ Z ) ) C_ ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    cY
    cA
    wss
    cZ
    cA
    wss
    w3a
    #
    wa
    cX
    c0
    wne
    cY
    cZ
    c.pl
    co
    #
    c0
    wne
    wa
    cY
    c0
    wne
    cZ
    c0
    wne
    wa
    wa
    #
    cX
    @2
    c.pl
    co
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    wss
    #
    @0
    @1
    @3
    @4
    cA
    c.pl
    cK
    cjn
    cfv
    #
    cK
    cK
    cple
    cfv
    #
    cX
    cY
    cZ
    @6
    eqid
    @5
    eqid
    paddass.a
    paddass.p
    paddasslem16
    3expa
    @0
    @1
    @3
    wn
    @4
    cA
    c.pl
    cK
    cX
    cY
    cZ
    paddass.a
    paddass.p
    paddasslem17
    3expa
    pm2.61dan
end
