include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "latjcom.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "latjass.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "simpr3.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"

theorem latj12
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .\/ ( Y .\/ Z ) ) = ( Y .\/ ( X .\/ Z ) ) )

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
    cX
    cY
    c.or
    co
    #
    cZ
    c.or
    co
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
    cY
    cZ
    c.or
    co
    c.or
    co
    cY
    cX
    cZ
    c.or
    co
    c.or
    co
    #
    @5
    @6
    @7
    cZ
    c.or
    @0
    @1
    @2
    @6
    @7
    wceq
    @3
    cB
    c.or
    cK
    cX
    cY
    latjass.b
    latjass.j
    latjcom
    3adant3r3
    oveq1d
    cB
    c.or
    cK
    cX
    cY
    cZ
    latjass.b
    latjass.j
    latjass
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
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr3
    cB
    c.or
    cK
    cY
    cX
    cZ
    latjass.b
    latjass.j
    latjass
    syl13anc
    3eqtr3d
end
