include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "simpl.mm"
include "latjcl.mm"
include "3anidm23.mm"
include "simpr.mm"
include "wbr.mm"
include "latref.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "latlej1.mm"
include "latasymd.mm"

theorem latjidm
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  assume latidm.b: |- B = ( Base ` K )
  assume latidm.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ X e. B ) -> ( X .\/ X ) = X )

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
    c.or
    co
    #
    cX
    latidm.b
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
    c.or
    cK
    cX
    cX
    latidm.b
    latidm.j
    latjcl
    3anidm23
    @0
    @1
    simpr
    #
    @2
    cX
    cX
    @3
    wbr
    #
    @8
    @4
    cX
    @3
    wbr
    #
    cB
    cK
    @3
    cX
    latidm.b
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
    c.or
    cK
    @3
    cX
    cX
    cX
    latidm.b
    @5
    latidm.j
    latjle12
    syl13anc
    mpbi2and
    @0
    @1
    cX
    @4
    @3
    wbr
    cB
    c.or
    cK
    @3
    cX
    cX
    latidm.b
    @5
    latidm.j
    latlej1
    3anidm23
    latasymd
end
