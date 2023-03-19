include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "latj31.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr2.mm"
include "simpr1.mm"
include "latj32.mm"
include "syl13anc.mm"
include "eqtrd.mm"

theorem latjrot
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latjass.b: |- B = ( Base ` K )
  assume latjass.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .\/ Y ) .\/ Z ) = ( ( Z .\/ X ) .\/ Y ) )

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
    cZ
    c.or
    co
    cZ
    cY
    c.or
    co
    cX
    c.or
    co
    #
    cZ
    cX
    c.or
    co
    cY
    c.or
    co
    #
    cB
    c.or
    cK
    cX
    cY
    cZ
    latjass.b
    latjass.j
    latj31
    @5
    @0
    @3
    @2
    @1
    @6
    @7
    wceq
    @0
    @4
    simpl
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
    @0
    @1
    @2
    @3
    simpr1
    cB
    c.or
    cK
    cZ
    cY
    cX
    latjass.b
    latjass.j
    latj32
    syl13anc
    eqtrd
end
