include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "eqid.mm"
include "latlej1.mm"
include "wb.mm"
include "latjcl.mm"
include "latleeqm1.mm"
include "syld3an3.mm"
include "mpbid.mm"

theorem latabs2
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latabs1.b: |- B = ( Base ` K )
  assume latabs1.j: |- .\/ = ( join ` K )
  assume latabs1.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X ./\ ( X .\/ Y ) ) = X )

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
    cX
    cY
    c.or
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    @3
    c.an
    co
    cX
    wceq
    #
    cB
    c.or
    cK
    @4
    cX
    cY
    latabs1.b
    @4
    eqid
    #
    latabs1.j
    latlej1
    @0
    @1
    @2
    @3
    cB
    wcel
    @5
    @6
    wb
    cB
    c.or
    cK
    cX
    cY
    latabs1.b
    latabs1.j
    latjcl
    cB
    cK
    @4
    c.an
    cX
    @3
    latabs1.b
    @7
    latabs1.m
    latleeqm1
    syld3an3
    mpbid
end
