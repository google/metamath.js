include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "ollat.mm"
include "adantr.mm"
include "simpr3.mm"
include "latmidm.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "latm4.mm"
include "syl122anc.mm"
include "eqtr3d.mm"

theorem latmmdir
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume olmass.b: |- B = ( Base ` K )
  assume olmass.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. OL /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X ./\ Y ) ./\ Z ) = ( ( X ./\ Z ) ./\ ( Y ./\ Z ) ) )

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
    cZ
    c.an
    co
    #
    c.an
    co
    #
    @6
    cZ
    c.an
    co
    cX
    cZ
    c.an
    co
    cY
    cZ
    c.an
    co
    c.an
    co
    #
    @5
    @7
    cZ
    @6
    c.an
    @5
    cK
    clat
    wcel
    #
    @3
    @7
    cZ
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
    simpr3
    #
    cB
    cK
    c.an
    cZ
    olmass.b
    olmass.m
    latmidm
    syl2anc
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
    @11
    @11
    cB
    cK
    c.an
    cZ
    cX
    cY
    cZ
    olmass.b
    olmass.m
    latm4
    syl122anc
    eqtr3d
end
