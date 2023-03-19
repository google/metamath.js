include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "latmle1.mm"
include "biantrurd.mm"
include "latleeqm1.mm"
include "necon3bbid.mm"
include "wb.mm"
include "simp1.mm"
include "latmcl.mm"
include "simp2.mm"
include "pltval.mm"
include "syl3anc.mm"
include "3bitr4d.mm"

theorem latnlemlt
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latnlemlt.b: |- B = ( Base ` K )
  assume latnlemlt.l: |- .<_ = ( le ` K )
  assume latnlemlt.s: |- .< = ( lt ` K )
  assume latnlemlt.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( -. X .<_ Y <-> ( X ./\ Y ) .< X ) )

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
    #
    cX
    cY
    c.an
    co
    #
    cX
    wne
    #
    @4
    cX
    c.le
    wbr
    #
    @5
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    wn
    @4
    cX
    c.lt
    wbr
    #
    @3
    @6
    @5
    cB
    cK
    c.le
    c.an
    cX
    cY
    latnlemlt.b
    latnlemlt.l
    latnlemlt.m
    latmle1
    biantrurd
    @3
    @8
    @4
    cX
    cB
    cK
    c.le
    c.an
    cX
    cY
    latnlemlt.b
    latnlemlt.l
    latnlemlt.m
    latleeqm1
    necon3bbid
    @3
    @0
    @4
    cB
    wcel
    @1
    @9
    @7
    wb
    @0
    @1
    @2
    simp1
    cB
    cK
    c.an
    cX
    cY
    latnlemlt.b
    latnlemlt.m
    latmcl
    @0
    @1
    @2
    simp2
    clat
    cB
    cB
    c.lt
    cK
    c.le
    @4
    cX
    latnlemlt.l
    latnlemlt.s
    pltval
    syl3anc
    3bitr4d
end
