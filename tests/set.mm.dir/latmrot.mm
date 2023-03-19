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
include "latmcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "latmcom.mm"
include "simpl.mm"
include "latmassOLD.mm"
include "syl13anc.mm"
include "eqtr4d.mm"

theorem latmrot
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume olmass.b: |- B = ( Base ` K )
  assume olmass.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. OL /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X ./\ Y ) ./\ Z ) = ( ( Z ./\ X ) ./\ Y ) )

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
    #
    cZ
    @6
    c.an
    co
    #
    cZ
    cX
    c.an
    co
    cY
    c.an
    co
    #
    @5
    cK
    clat
    wcel
    #
    @6
    cB
    wcel
    #
    @3
    @7
    @8
    wceq
    @0
    @10
    @4
    cK
    ollat
    adantr
    #
    @5
    @10
    @1
    @2
    @11
    @12
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
    latmcl
    syl3anc
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    cK
    c.an
    @6
    cZ
    olmass.b
    olmass.m
    latmcom
    syl3anc
    @5
    @0
    @3
    @1
    @2
    @9
    @8
    wceq
    @0
    @4
    simpl
    @15
    @13
    @14
    cB
    cK
    c.an
    cZ
    cX
    cY
    olmass.b
    olmass.m
    latmassOLD
    syl13anc
    eqtr4d
end
