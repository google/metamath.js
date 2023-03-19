include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "latj12.mm"
include "syl13anc.mm"
include "oveq2d.mm"
include "simp2l.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latjass.mm"
include "3eqtr4d.mm"

theorem latj4
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X .\/ Y ) .\/ ( Z .\/ W ) ) = ( ( X .\/ Z ) .\/ ( Y .\/ W ) ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cY
    cZ
    cW
    c.or
    co
    #
    c.or
    co
    #
    c.or
    co
    #
    cX
    cZ
    cY
    cW
    c.or
    co
    #
    c.or
    co
    #
    c.or
    co
    #
    cX
    cY
    c.or
    co
    @8
    c.or
    co
    #
    cX
    cZ
    c.or
    co
    @11
    c.or
    co
    #
    @7
    @9
    @12
    cX
    c.or
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
    cB
    c.or
    cK
    cY
    cZ
    cW
    latjass.b
    latjass.j
    latj12
    syl13anc
    oveq2d
    @7
    @0
    @1
    @2
    @8
    cB
    wcel
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
    cB
    c.or
    cK
    cZ
    cW
    latjass.b
    latjass.j
    latjcl
    syl3anc
    cB
    c.or
    cK
    cX
    cY
    @8
    latjass.b
    latjass.j
    latjass
    syl13anc
    @7
    @0
    @1
    @4
    @11
    cB
    wcel
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
    cB
    c.or
    cK
    cY
    cW
    latjass.b
    latjass.j
    latjcl
    syl3anc
    cB
    c.or
    cK
    cX
    cZ
    @11
    latjass.b
    latjass.j
    latjass
    syl13anc
    3eqtr4d
end
