include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "paddcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "paddass.mm"
include "simpl.mm"
include "simpr3.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"

theorem padd12N
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume paddass.a: |- A = ( Atoms ` K )
  assume paddass.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) ) -> ( X .+ ( Y .+ Z ) ) = ( Y .+ ( X .+ Z ) ) )

  proof
    cK
    chlt
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
    cZ
    cA
    wss
    #
    w3a
    #
    wa
    #
    cX
    cY
    c.pl
    co
    #
    cZ
    c.pl
    co
    cY
    cX
    c.pl
    co
    #
    cZ
    c.pl
    co
    #
    cX
    cY
    cZ
    c.pl
    co
    c.pl
    co
    cY
    cX
    cZ
    c.pl
    co
    c.pl
    co
    #
    @5
    @6
    @7
    cZ
    c.pl
    @5
    cK
    clat
    wcel
    #
    @1
    @2
    @6
    @7
    wceq
    @0
    @10
    @4
    cK
    hllat
    adantr
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    cA
    c.pl
    cK
    cX
    cY
    paddass.a
    paddass.p
    paddcom
    syl3anc
    oveq1d
    cA
    c.pl
    cK
    cX
    cY
    cZ
    paddass.a
    paddass.p
    paddass
    @5
    @0
    @2
    @1
    @3
    @8
    @9
    wceq
    @0
    @4
    simpl
    @12
    @11
    @0
    @1
    @2
    @3
    simpr3
    cA
    c.pl
    cK
    cY
    cX
    cZ
    paddass.a
    paddass.p
    paddass
    syl13anc
    3eqtr3d
end
