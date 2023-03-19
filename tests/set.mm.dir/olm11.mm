include "col.mm"
include "wcel.mm"
include "wa.mm"
include "coc.mm"
include "cfv.mm"
include "cjn.mm"
include "co.mm"
include "cp0.mm"
include "cops.mm"
include "wceq.mm"
include "olop.mm"
include "adantr.mm"
include "eqid.mm"
include "opoc1.mm"
include "syl.mm"
include "oveq2d.mm"
include "opoccl.mm"
include "sylan.mm"
include "olj01.mm"
include "syldan.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "op1cl.mm"
include "oldmj4.mm"
include "mpd3an3.mm"
include "opococ.mm"
include "3eqtr3d.mm"

theorem olm11
  let cB: class B
  let c.1: class .1.
  let cK: class K
  let c.an: class ./\
  let cX: class X
  assume olm1.b: |- B = ( Base ` K )
  assume olm1.m: |- ./\ = ( meet ` K )
  assume olm1.u: |- .1. = ( 1. ` K )


  assert |- ( ( K e. OL /\ X e. B ) -> ( X ./\ .1. ) = X )

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
    cK
    coc
    cfv
    #
    cfv
    #
    c.1
    @3
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    @3
    cfv
    #
    @4
    @3
    cfv
    #
    cX
    c.1
    c.an
    co
    #
    cX
    @2
    @7
    @4
    @3
    @2
    @7
    @4
    cK
    cp0
    cfv
    #
    @6
    co
    #
    @4
    @2
    @5
    @11
    @4
    @6
    @2
    cK
    cops
    wcel
    #
    @5
    @11
    wceq
    @0
    @13
    @1
    cK
    olop
    #
    adantr
    #
    c.1
    cK
    @3
    @11
    @11
    eqid
    #
    olm1.u
    @3
    eqid
    #
    opoc1
    syl
    oveq2d
    @0
    @1
    @4
    cB
    wcel
    #
    @12
    @4
    wceq
    @0
    @13
    @1
    @18
    @14
    cB
    cK
    @3
    cX
    olm1.b
    @17
    opoccl
    sylan
    cB
    @6
    cK
    @4
    @11
    olm1.b
    @6
    eqid
    #
    @16
    olj01
    syldan
    eqtrd
    fveq2d
    @0
    @1
    c.1
    cB
    wcel
    #
    @8
    @10
    wceq
    @2
    @13
    @20
    @15
    cB
    c.1
    cK
    olm1.b
    olm1.u
    op1cl
    syl
    cB
    @6
    cK
    c.an
    @3
    cX
    c.1
    olm1.b
    @19
    olm1.m
    @17
    oldmj4
    mpd3an3
    @0
    @13
    @1
    @9
    cX
    wceq
    @14
    cB
    cK
    @3
    cX
    olm1.b
    @17
    opococ
    sylan
    3eqtr3d
end
