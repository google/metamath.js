include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "jca.mm"
include "latj4.mm"
include "syld3an3.mm"
include "simp2l.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem latj4rot
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X .\/ Y ) .\/ ( Z .\/ W ) ) = ( ( W .\/ X ) .\/ ( Y .\/ Z ) ) )

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
    c.or
    co
    #
    cZ
    cW
    c.or
    co
    #
    c.or
    co
    @8
    cW
    cZ
    c.or
    co
    #
    c.or
    co
    #
    cX
    cW
    c.or
    co
    #
    cY
    cZ
    c.or
    co
    #
    c.or
    co
    #
    cW
    cX
    c.or
    co
    #
    @13
    c.or
    co
    @7
    @9
    @10
    @8
    c.or
    @7
    @0
    @4
    @5
    @9
    @10
    wceq
    @0
    @3
    @6
    simp1
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
    cZ
    cW
    latjass.b
    latjass.j
    latjcom
    syl3anc
    oveq2d
    @0
    @3
    @6
    @5
    @4
    wa
    @11
    @14
    wceq
    @7
    @5
    @4
    @18
    @17
    jca
    cB
    c.or
    cK
    cZ
    cX
    cY
    cW
    latjass.b
    latjass.j
    latj4
    syld3an3
    @7
    @12
    @15
    @13
    c.or
    @7
    @0
    @1
    @5
    @12
    @15
    wceq
    @16
    @0
    @1
    @2
    @6
    simp2l
    @18
    cB
    c.or
    cK
    cX
    cW
    latjass.b
    latjass.j
    latjcom
    syl3anc
    oveq1d
    3eqtrd
end
