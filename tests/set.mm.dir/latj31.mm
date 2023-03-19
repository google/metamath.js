include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr1.mm"
include "simpr2.mm"
include "latj12.mm"
include "syl13anc.mm"
include "latjcl.mm"
include "3adant3r3.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem latj31
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .\/ Y ) .\/ Z ) = ( ( Z .\/ Y ) .\/ X ) )

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
    cZ
    cX
    cY
    c.or
    co
    #
    c.or
    co
    #
    cX
    cZ
    cY
    c.or
    co
    #
    c.or
    co
    #
    @6
    cZ
    c.or
    co
    #
    @8
    cX
    c.or
    co
    #
    @5
    @0
    @3
    @1
    @2
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
    simpr3
    #
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
    cB
    c.or
    cK
    cZ
    cX
    cY
    latjass.b
    latjass.j
    latj12
    syl13anc
    @5
    @0
    @6
    cB
    wcel
    #
    @3
    @10
    @7
    wceq
    @12
    @0
    @1
    @2
    @16
    @3
    cB
    c.or
    cK
    cX
    cY
    latjass.b
    latjass.j
    latjcl
    3adant3r3
    @13
    cB
    c.or
    cK
    @6
    cZ
    latjass.b
    latjass.j
    latjcom
    syl3anc
    @5
    @0
    @8
    cB
    wcel
    #
    @1
    @11
    @9
    wceq
    @12
    @5
    @0
    @3
    @2
    @17
    @12
    @13
    @15
    cB
    c.or
    cK
    cZ
    cY
    latjass.b
    latjass.j
    latjcl
    syl3anc
    @14
    cB
    c.or
    cK
    @8
    cX
    latjass.b
    latjass.j
    latjcom
    syl3anc
    3eqtr4d
end
