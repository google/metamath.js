include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simpr1.mm"
include "latj32.mm"
include "syl13anc.mm"
include "latjcl.mm"
include "3adant3r1.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem latj13
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .\/ ( Y .\/ Z ) ) = ( Z .\/ ( Y .\/ X ) ) )

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
    cZ
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cY
    cZ
    c.or
    co
    #
    cX
    c.or
    co
    #
    cY
    cX
    c.or
    co
    #
    cZ
    c.or
    co
    #
    cX
    @6
    c.or
    co
    #
    cZ
    @8
    c.or
    co
    #
    @5
    @0
    @2
    @3
    @1
    @7
    @9
    wceq
    @0
    @4
    simpl
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
    simpr3
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cB
    c.or
    cK
    cY
    cZ
    cX
    latjass.b
    latjass.j
    latj32
    syl13anc
    @5
    @0
    @1
    @6
    cB
    wcel
    #
    @10
    @7
    wceq
    @12
    @15
    @0
    @2
    @3
    @16
    @1
    cB
    c.or
    cK
    cY
    cZ
    latjass.b
    latjass.j
    latjcl
    3adant3r1
    cB
    c.or
    cK
    cX
    @6
    latjass.b
    latjass.j
    latjcom
    syl3anc
    @5
    @0
    @3
    @8
    cB
    wcel
    #
    @11
    @9
    wceq
    @12
    @14
    @5
    @0
    @2
    @1
    @17
    @12
    @13
    @15
    cB
    c.or
    cK
    cY
    cX
    latjass.b
    latjass.j
    latjcl
    syl3anc
    cB
    c.or
    cK
    cZ
    @8
    latjass.b
    latjass.j
    latjcom
    syl3anc
    3eqtr4d
end
