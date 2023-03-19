include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "latref.mm"
include "3adant2.mm"
include "biantrud.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "bitrd.mm"
include "latlej2.mm"
include "cpo.mm"
include "latpos.mm"
include "3ad2ant1.mm"
include "latjcl.mm"
include "posasymb.mm"
include "syl3anc.mm"

theorem latleeqj1
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume latlej.b: |- B = ( Base ` K )
  assume latlej.l: |- .<_ = ( le ` K )
  assume latlej.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> ( X .\/ Y ) = Y ) )

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
    c.le
    wbr
    #
    cX
    cY
    c.or
    co
    #
    cY
    c.le
    wbr
    #
    cY
    @5
    c.le
    wbr
    #
    wa
    #
    @5
    cY
    wceq
    #
    @3
    @4
    @6
    @8
    @3
    @4
    @4
    cY
    cY
    c.le
    wbr
    #
    wa
    #
    @6
    @3
    @10
    @4
    @0
    @2
    @10
    @1
    cB
    cK
    c.le
    cY
    latlej.b
    latlej.l
    latref
    3adant2
    biantrud
    @3
    @0
    @1
    @2
    @2
    @11
    @6
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    #
    @12
    cB
    c.or
    cK
    c.le
    cX
    cY
    cY
    latlej.b
    latlej.l
    latlej.j
    latjle12
    syl13anc
    bitrd
    @3
    @7
    @6
    cB
    c.or
    cK
    c.le
    cX
    cY
    latlej.b
    latlej.l
    latlej.j
    latlej2
    biantrud
    bitrd
    @3
    cK
    cpo
    wcel
    #
    @5
    cB
    wcel
    @2
    @8
    @9
    wb
    @0
    @1
    @13
    @2
    cK
    latpos
    3ad2ant1
    cB
    c.or
    cK
    cX
    cY
    latlej.b
    latlej.j
    latjcl
    @12
    cB
    cK
    c.le
    @5
    cY
    latlej.b
    latlej.l
    posasymb
    syl3anc
    bitrd
end
