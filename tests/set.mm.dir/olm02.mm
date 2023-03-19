include "col.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "ollat.mm"
include "adantr.mm"
include "simpr.mm"
include "cops.mm"
include "olop.mm"
include "op0cl.mm"
include "syl.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "olm01.mm"
include "eqtr3d.mm"

theorem olm02
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume olm0.b: |- B = ( Base ` K )
  assume olm0.m: |- ./\ = ( meet ` K )
  assume olm0.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OL /\ X e. B ) -> ( .0. ./\ X ) = .0. )

  proof
    cK
    col
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    c.0
    c.an
    co
    #
    c.0
    cX
    c.an
    co
    #
    c.0
    @2
    cK
    clat
    wcel
    #
    @1
    c.0
    cB
    wcel
    #
    @3
    @4
    wceq
    @0
    @5
    @1
    cK
    ollat
    adantr
    @0
    @1
    simpr
    @2
    cK
    cops
    wcel
    #
    @6
    @0
    @7
    @1
    cK
    olop
    adantr
    cB
    cK
    c.0
    olm0.b
    olm0.z
    op0cl
    syl
    cB
    cK
    c.an
    cX
    c.0
    olm0.b
    olm0.m
    latmcom
    syl3anc
    cB
    cK
    c.an
    cX
    c.0
    olm0.b
    olm0.m
    olm0.z
    olm01
    eqtr3d
end
