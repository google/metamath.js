include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr2.mm"
include "simpr1.mm"
include "paddasslem18.mm"
include "syl13anc.mm"
include "wceq.mm"
include "clat.mm"
include "hllat.mm"
include "paddcom.mm"
include "syl3an1.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "3sstr4d.mm"
include "eqssd.mm"

theorem paddass
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume paddass.a: |- A = ( Atoms ` K )
  assume paddass.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) ) -> ( ( X .+ Y ) .+ Z ) = ( X .+ ( Y .+ Z ) ) )

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
    #
    cX
    cY
    cZ
    c.pl
    co
    #
    c.pl
    co
    #
    @5
    cZ
    cY
    cX
    c.pl
    co
    #
    c.pl
    co
    #
    cZ
    cY
    c.pl
    co
    #
    cX
    c.pl
    co
    #
    @7
    @9
    @5
    @0
    @3
    @2
    @1
    @11
    @13
    wss
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cA
    c.pl
    cK
    cZ
    cY
    cX
    paddass.a
    paddass.p
    paddasslem18
    syl13anc
    @5
    @7
    @10
    cZ
    c.pl
    co
    #
    @11
    @5
    @6
    @10
    cZ
    c.pl
    @0
    @1
    @2
    @6
    @10
    wceq
    #
    @3
    @0
    cK
    clat
    wcel
    #
    @1
    @2
    @19
    cK
    hllat
    #
    cA
    c.pl
    cK
    cX
    cY
    paddass.a
    paddass.p
    paddcom
    syl3an1
    3adant3r3
    oveq1d
    @5
    @0
    @10
    cA
    wss
    #
    @3
    @18
    @11
    wceq
    #
    @14
    @5
    @0
    @2
    @1
    @22
    @14
    @16
    @17
    cA
    chlt
    c.pl
    cK
    cY
    cX
    paddass.a
    paddass.p
    paddssat
    syl3anc
    @15
    @0
    @20
    @22
    @3
    @23
    @21
    cA
    c.pl
    cK
    @10
    cZ
    paddass.a
    paddass.p
    paddcom
    syl3an1
    syl3anc
    eqtrd
    @5
    @9
    cX
    @12
    c.pl
    co
    #
    @13
    @5
    @8
    @12
    cX
    c.pl
    @0
    @2
    @3
    @8
    @12
    wceq
    #
    @1
    @0
    @20
    @2
    @3
    @25
    @21
    cA
    c.pl
    cK
    cY
    cZ
    paddass.a
    paddass.p
    paddcom
    syl3an1
    3adant3r1
    oveq2d
    @5
    @0
    @1
    @12
    cA
    wss
    #
    @24
    @13
    wceq
    #
    @14
    @17
    @5
    @0
    @3
    @2
    @26
    @14
    @15
    @16
    cA
    chlt
    c.pl
    cK
    cZ
    cY
    paddass.a
    paddass.p
    paddssat
    syl3anc
    @0
    @20
    @1
    @26
    @27
    @21
    cA
    c.pl
    cK
    cX
    @12
    paddass.a
    paddass.p
    paddcom
    syl3an1
    syl3anc
    eqtrd
    3sstr4d
    cA
    c.pl
    cK
    cX
    cY
    cZ
    paddass.a
    paddass.p
    paddasslem18
    eqssd
end
