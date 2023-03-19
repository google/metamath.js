include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "padd12N.mm"
include "syl13anc.mm"
include "oveq2d.mm"
include "simp2l.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "paddass.mm"
include "3eqtr4d.mm"

theorem padd4N
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume paddass.a: |- A = ( Atoms ` K )
  assume paddass.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X C_ A /\ Y C_ A ) /\ ( Z C_ A /\ W C_ A ) ) -> ( ( X .+ Y ) .+ ( Z .+ W ) ) = ( ( X .+ Z ) .+ ( Y .+ W ) ) )

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
    wa
    #
    cZ
    cA
    wss
    #
    cW
    cA
    wss
    #
    wa
    #
    w3a
    #
    cX
    cY
    cZ
    cW
    c.pl
    co
    #
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cZ
    cY
    cW
    c.pl
    co
    #
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cY
    c.pl
    co
    @8
    c.pl
    co
    #
    cX
    cZ
    c.pl
    co
    @11
    c.pl
    co
    #
    @7
    @9
    @12
    cX
    c.pl
    @7
    @0
    @2
    @4
    @5
    @9
    @12
    wceq
    @0
    @3
    @6
    simp1
    #
    @0
    @1
    @2
    @6
    simp2r
    #
    @0
    @3
    @4
    @5
    simp3l
    #
    @0
    @3
    @4
    @5
    simp3r
    #
    cA
    c.pl
    cK
    cY
    cZ
    cW
    paddass.a
    paddass.p
    padd12N
    syl13anc
    oveq2d
    @7
    @0
    @1
    @2
    @8
    cA
    wss
    #
    @14
    @10
    wceq
    @16
    @0
    @1
    @2
    @6
    simp2l
    #
    @17
    @7
    @0
    @4
    @5
    @20
    @16
    @18
    @19
    cA
    chlt
    c.pl
    cK
    cZ
    cW
    paddass.a
    paddass.p
    paddssat
    syl3anc
    cA
    c.pl
    cK
    cX
    cY
    @8
    paddass.a
    paddass.p
    paddass
    syl13anc
    @7
    @0
    @1
    @4
    @11
    cA
    wss
    #
    @15
    @13
    wceq
    @16
    @21
    @18
    @7
    @0
    @2
    @5
    @22
    @16
    @17
    @19
    cA
    chlt
    c.pl
    cK
    cY
    cW
    paddass.a
    paddass.p
    paddssat
    syl3anc
    cA
    c.pl
    cK
    cX
    cZ
    @11
    paddass.a
    paddass.p
    paddass
    syl13anc
    3eqtr4d
end
