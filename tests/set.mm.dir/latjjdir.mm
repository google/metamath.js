include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "latjidm.mm"
include "3ad2antr3.mm"
include "oveq2d.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "latj4.mm"
include "syl122anc.mm"
include "eqtr3d.mm"

theorem latjjdir
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .\/ Y ) .\/ Z ) = ( ( X .\/ Z ) .\/ ( Y .\/ Z ) ) )

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
    cZ
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
    cX
    cZ
    c.or
    co
    cY
    cZ
    c.or
    co
    c.or
    co
    #
    @5
    @7
    cZ
    @6
    c.or
    @0
    @1
    @3
    @7
    cZ
    wceq
    @2
    cB
    c.or
    cK
    cZ
    latjass.b
    latjass.j
    latjidm
    3ad2antr3
    oveq2d
    @5
    @0
    @1
    @2
    @3
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
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    #
    @10
    cB
    c.or
    cK
    cZ
    cX
    cY
    cZ
    latjass.b
    latjass.j
    latj4
    syl122anc
    eqtr3d
end
