include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "latref.mm"
include "3adant3.mm"
include "biantrurd.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "bitrd.mm"
include "latmle1.mm"
include "cpo.mm"
include "latpos.mm"
include "3ad2ant1.mm"
include "latmcl.mm"
include "posasymb.mm"
include "syl3anc.mm"

theorem latleeqm1
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latmle.b: |- B = ( Base ` K )
  assume latmle.l: |- .<_ = ( le ` K )
  assume latmle.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> ( X ./\ Y ) = X ) )

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
    c.an
    co
    #
    cX
    c.le
    wbr
    #
    cX
    @5
    c.le
    wbr
    #
    wa
    #
    @5
    cX
    wceq
    #
    @3
    @4
    @7
    @8
    @3
    @4
    cX
    cX
    c.le
    wbr
    #
    @4
    wa
    #
    @7
    @3
    @10
    @4
    @0
    @1
    @10
    @2
    cB
    cK
    c.le
    cX
    latmle.b
    latmle.l
    latref
    3adant3
    biantrurd
    @3
    @0
    @1
    @1
    @2
    @11
    @7
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    #
    @12
    @0
    @1
    @2
    simp3
    cB
    cK
    c.le
    c.an
    cX
    cX
    cY
    latmle.b
    latmle.l
    latmle.m
    latlem12
    syl13anc
    bitrd
    @3
    @6
    @7
    cB
    cK
    c.le
    c.an
    cX
    cY
    latmle.b
    latmle.l
    latmle.m
    latmle1
    biantrurd
    bitrd
    @3
    cK
    cpo
    wcel
    #
    @5
    cB
    wcel
    @1
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
    cK
    c.an
    cX
    cY
    latmle.b
    latmle.m
    latmcl
    @12
    cB
    cK
    c.le
    @5
    cX
    latmle.b
    latmle.l
    posasymb
    syl3anc
    bitrd
end
