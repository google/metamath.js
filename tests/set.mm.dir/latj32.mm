include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "latjcom.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "latjass.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpr2.mm"
include "3jca.mm"
include "syldan.mm"
include "3eqtr4d.mm"

theorem latj32
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .\/ Y ) .\/ Z ) = ( ( X .\/ Z ) .\/ Y ) )

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
    cZ
    c.or
    co
    #
    c.or
    co
    cX
    cZ
    cY
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
    cZ
    c.or
    co
    cX
    cZ
    c.or
    co
    cY
    c.or
    co
    #
    @5
    @6
    @7
    cX
    c.or
    @0
    @2
    @3
    @6
    @7
    wceq
    @1
    cB
    c.or
    cK
    cY
    cZ
    latjass.b
    latjass.j
    latjcom
    3adant3r1
    oveq2d
    cB
    c.or
    cK
    cX
    cY
    cZ
    latjass.b
    latjass.j
    latjass
    @0
    @4
    @1
    @3
    @2
    w3a
    @9
    @8
    wceq
    @5
    @1
    @3
    @2
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
    @0
    @1
    @2
    @3
    simpr2
    3jca
    cB
    c.or
    cK
    cX
    cZ
    cY
    latjass.b
    latjass.j
    latjass
    syldan
    3eqtr4d
end
