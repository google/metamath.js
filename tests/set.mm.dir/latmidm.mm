include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "simpl.mm"
include "latmcl.mm"
include "3anidm23.mm"
include "simpr.mm"
include "wbr.mm"
include "latmle1.mm"
include "latref.mm"
include "wb.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "latasymd.mm"

theorem latmidm
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  assume latmidm.b: |- B = ( Base ` K )
  assume latmidm.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B ) -> ( X ./\ X ) = X )

  proof
    cK
    clat
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
    cX
    c.an
    co
    #
    cX
    latmidm.b
    @3
    eqid
    #
    @0
    @1
    simpl
    #
    @0
    @1
    @4
    cB
    wcel
    cB
    cK
    c.an
    cX
    cX
    latmidm.b
    latmidm.m
    latmcl
    3anidm23
    @0
    @1
    simpr
    #
    @0
    @1
    @4
    cX
    @3
    wbr
    cB
    cK
    @3
    c.an
    cX
    cX
    latmidm.b
    @5
    latmidm.m
    latmle1
    3anidm23
    @2
    cX
    cX
    @3
    wbr
    #
    @8
    cX
    @4
    @3
    wbr
    #
    cB
    cK
    @3
    cX
    latmidm.b
    @5
    latref
    #
    @10
    @2
    @0
    @1
    @1
    @1
    @8
    @8
    wa
    @9
    wb
    @6
    @7
    @7
    @7
    cB
    cK
    @3
    c.an
    cX
    cX
    cX
    latmidm.b
    @5
    latmidm.m
    latlem12
    syl13anc
    mpbi2and
    latasymd
end
