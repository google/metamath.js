include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "clat.mm"
include "ollat.mm"
include "latmcom.mm"
include "syl3an1.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "latmassOLD.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpr2.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"

theorem latm32
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume olmass.b: |- B = ( Base ` K )
  assume olmass.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. OL /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X ./\ Y ) ./\ Z ) = ( ( X ./\ Z ) ./\ Y ) )

  proof
    cK
    col
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
    c.an
    co
    #
    c.an
    co
    cX
    cZ
    cY
    c.an
    co
    #
    c.an
    co
    #
    cX
    cY
    c.an
    co
    cZ
    c.an
    co
    cX
    cZ
    c.an
    co
    cY
    c.an
    co
    #
    @5
    @6
    @7
    cX
    c.an
    @0
    @2
    @3
    @6
    @7
    wceq
    #
    @1
    @0
    cK
    clat
    wcel
    @2
    @3
    @10
    cK
    ollat
    cB
    cK
    c.an
    cY
    cZ
    olmass.b
    olmass.m
    latmcom
    syl3an1
    3adant3r1
    oveq2d
    cB
    cK
    c.an
    cX
    cY
    cZ
    olmass.b
    olmass.m
    latmassOLD
    @5
    @0
    @1
    @3
    @2
    @9
    @8
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
    simpr3
    @0
    @1
    @2
    @3
    simpr2
    cB
    cK
    c.an
    cX
    cZ
    cY
    olmass.b
    olmass.m
    latmassOLD
    syl13anc
    3eqtr4d
end
