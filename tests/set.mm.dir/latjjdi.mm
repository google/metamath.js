include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpr1.mm"
include "latjidm.mm"
include "syldan.mm"
include "oveq1d.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "latj4.mm"
include "syl122anc.mm"
include "eqtr3d.mm"

theorem latjjdi
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .\/ ( Y .\/ Z ) ) = ( ( X .\/ Y ) .\/ ( X .\/ Z ) ) )

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
    cX
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
    cX
    @7
    c.or
    co
    cX
    cY
    c.or
    co
    cX
    cZ
    c.or
    co
    c.or
    co
    #
    @5
    @6
    cX
    @7
    c.or
    @0
    @4
    @1
    @6
    cX
    wceq
    @0
    @1
    @2
    @3
    simpr1
    #
    cB
    c.or
    cK
    cX
    latjass.b
    latjass.j
    latjidm
    syldan
    oveq1d
    @5
    @0
    @1
    @1
    @2
    @3
    @8
    @9
    wceq
    @0
    @4
    simpl
    @10
    @10
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
    cB
    c.or
    cK
    cZ
    cX
    cX
    cY
    latjass.b
    latjass.j
    latj4
    syl122anc
    eqtr3d
end
