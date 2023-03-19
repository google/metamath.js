include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "eqid.mm"
include "latmle1.mm"
include "wb.mm"
include "latmcl.mm"
include "latleeqj2.mm"
include "3com23.mm"
include "syld3an3.mm"
include "mpbid.mm"

theorem latabs1
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latabs1.b: |- B = ( Base ` K )
  assume latabs1.j: |- .\/ = ( join ` K )
  assume latabs1.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .\/ ( X ./\ Y ) ) = X )

  proof
    cK
    clat
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
    w3a
    cX
    cY
    c.an
    co
    #
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    @3
    c.or
    co
    cX
    wceq
    #
    cB
    cK
    @4
    c.an
    cX
    cY
    latabs1.b
    @4
    eqid
    #
    latabs1.m
    latmle1
    @0
    @1
    @2
    @3
    cB
    wcel
    #
    @5
    @6
    wb
    #
    cB
    cK
    c.an
    cX
    cY
    latabs1.b
    latabs1.m
    latmcl
    @0
    @8
    @1
    @9
    cB
    c.or
    cK
    @4
    @3
    cX
    latabs1.b
    @7
    latabs1.j
    latleeqj2
    3com23
    syld3an3
    mpbid
end
