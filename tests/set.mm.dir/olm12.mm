include "col.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "ollat.mm"
include "adantr.mm"
include "cops.mm"
include "olop.mm"
include "op1cl.mm"
include "syl.mm"
include "simpr.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "olm11.mm"
include "eqtrd.mm"

theorem olm12
  let cB: class B
  let c.1: class .1.
  let cK: class K
  let c.an: class ./\
  let cX: class X
  assume olm1.b: |- B = ( Base ` K )
  assume olm1.m: |- ./\ = ( meet ` K )
  assume olm1.u: |- .1. = ( 1. ` K )


  assert |- ( ( K e. OL /\ X e. B ) -> ( .1. ./\ X ) = X )

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
    c.1
    cX
    c.an
    co
    #
    cX
    c.1
    c.an
    co
    #
    cX
    @2
    cK
    clat
    wcel
    #
    c.1
    cB
    wcel
    #
    @1
    @3
    @4
    wceq
    @0
    @5
    @1
    cK
    ollat
    adantr
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
    c.1
    cK
    olm1.b
    olm1.u
    op1cl
    syl
    @0
    @1
    simpr
    cB
    cK
    c.an
    c.1
    cX
    olm1.b
    olm1.m
    latmcom
    syl3anc
    cB
    c.1
    cK
    c.an
    cX
    olm1.b
    olm1.m
    olm1.u
    olm11
    eqtrd
end
