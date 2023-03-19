include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "ollat.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "latmassOLD.mm"
include "simpr3.mm"
include "3jca.mm"
include "syldan.mm"
include "3eqtr3d.mm"

theorem latm12
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume olmass.b: |- B = ( Base ` K )
  assume olmass.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. OL /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X ./\ ( Y ./\ Z ) ) = ( Y ./\ ( X ./\ Z ) ) )

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
    c.an
    co
    #
    cZ
    c.an
    co
    cY
    cX
    c.an
    co
    #
    cZ
    c.an
    co
    #
    cX
    cY
    cZ
    c.an
    co
    c.an
    co
    cY
    cX
    cZ
    c.an
    co
    c.an
    co
    #
    @5
    @6
    @7
    cZ
    c.an
    @5
    cK
    clat
    wcel
    #
    @1
    @2
    @6
    @7
    wceq
    @0
    @10
    @4
    cK
    ollat
    adantr
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
    cK
    c.an
    cX
    cY
    olmass.b
    olmass.m
    latmcom
    syl3anc
    oveq1d
    cB
    cK
    c.an
    cX
    cY
    cZ
    olmass.b
    olmass.m
    latmassOLD
    @0
    @4
    @2
    @1
    @3
    w3a
    @8
    @9
    wceq
    @5
    @2
    @1
    @3
    @12
    @11
    @0
    @1
    @2
    @3
    simpr3
    3jca
    cB
    cK
    c.an
    cY
    cX
    cZ
    olmass.b
    olmass.m
    latmassOLD
    syldan
    3eqtr3d
end
