include "col.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "clat.mm"
include "ollat.mm"
include "adantr.mm"
include "simpr.mm"
include "cops.mm"
include "olop.mm"
include "op0cl.mm"
include "syl.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "wbr.mm"
include "latmle2.mm"
include "op0le.mm"
include "sylan.mm"
include "latref.mm"
include "syl2anc.mm"
include "wb.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "latasymd.mm"

theorem olm01
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume olm0.b: |- B = ( Base ` K )
  assume olm0.m: |- ./\ = ( meet ` K )
  assume olm0.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OL /\ X e. B ) -> ( X ./\ .0. ) = .0. )

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
    cB
    cK
    cK
    cple
    cfv
    #
    cX
    c.0
    c.an
    co
    #
    c.0
    olm0.b
    @3
    eqid
    #
    @0
    cK
    clat
    wcel
    #
    @1
    cK
    ollat
    adantr
    #
    @2
    @6
    @1
    c.0
    cB
    wcel
    #
    @4
    cB
    wcel
    @7
    @0
    @1
    simpr
    #
    @2
    cK
    cops
    wcel
    #
    @8
    @0
    @10
    @1
    cK
    olop
    #
    adantr
    cB
    cK
    c.0
    olm0.b
    olm0.z
    op0cl
    syl
    #
    cB
    cK
    c.an
    cX
    c.0
    olm0.b
    olm0.m
    latmcl
    syl3anc
    @12
    @2
    @6
    @1
    @8
    @4
    c.0
    @3
    wbr
    @7
    @9
    @12
    cB
    cK
    @3
    c.an
    cX
    c.0
    olm0.b
    @5
    olm0.m
    latmle2
    syl3anc
    @2
    c.0
    cX
    @3
    wbr
    #
    c.0
    c.0
    @3
    wbr
    #
    c.0
    @4
    @3
    wbr
    #
    @0
    @10
    @1
    @13
    @11
    cB
    cK
    @3
    cX
    c.0
    olm0.b
    @5
    olm0.z
    op0le
    sylan
    @2
    @6
    @8
    @14
    @7
    @12
    cB
    cK
    @3
    c.0
    olm0.b
    @5
    latref
    syl2anc
    @2
    @6
    @8
    @1
    @8
    @13
    @14
    wa
    @15
    wb
    @7
    @12
    @9
    @12
    cB
    cK
    @3
    c.an
    c.0
    cX
    c.0
    olm0.b
    @5
    olm0.m
    latlem12
    syl13anc
    mpbi2and
    latasymd
end
