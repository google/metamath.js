include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wi.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "latmlem1.mm"
include "syl13anc.mm"
include "simp3r.mm"
include "latmlem2.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "lattr.mm"
include "syl2and.mm"

theorem latmlem12
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latmle.b: |- B = ( Base ` K )
  assume latmle.l: |- .<_ = ( le ` K )
  assume latmle.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X .<_ Y /\ Z .<_ W ) -> ( X ./\ Z ) .<_ ( Y ./\ W ) ) )

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
    wa
    #
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cZ
    c.an
    co
    #
    cY
    cZ
    c.an
    co
    #
    c.le
    wbr
    #
    cZ
    cW
    c.le
    wbr
    #
    @10
    cY
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @9
    @13
    c.le
    wbr
    #
    @7
    @0
    @1
    @2
    @4
    @8
    @11
    wi
    @0
    @3
    @6
    simp1
    #
    @0
    @1
    @2
    @6
    simp2l
    #
    @0
    @1
    @2
    @6
    simp2r
    #
    @0
    @3
    @4
    @5
    simp3l
    #
    cB
    cK
    c.le
    c.an
    cX
    cY
    cZ
    latmle.b
    latmle.l
    latmle.m
    latmlem1
    syl13anc
    @7
    @0
    @4
    @5
    @2
    @12
    @14
    wi
    @16
    @19
    @0
    @3
    @4
    @5
    simp3r
    #
    @18
    cB
    cK
    c.le
    c.an
    cZ
    cW
    cY
    latmle.b
    latmle.l
    latmle.m
    latmlem2
    syl13anc
    @7
    @0
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @11
    @14
    wa
    @15
    wi
    @16
    @7
    @0
    @1
    @4
    @21
    @16
    @17
    @19
    cB
    cK
    c.an
    cX
    cZ
    latmle.b
    latmle.m
    latmcl
    syl3anc
    @7
    @0
    @2
    @4
    @22
    @16
    @18
    @19
    cB
    cK
    c.an
    cY
    cZ
    latmle.b
    latmle.m
    latmcl
    syl3anc
    @7
    @0
    @2
    @5
    @23
    @16
    @18
    @20
    cB
    cK
    c.an
    cY
    cW
    latmle.b
    latmle.m
    latmcl
    syl3anc
    cB
    cK
    c.le
    @9
    @10
    @13
    latmle.b
    latmle.l
    lattr
    syl13anc
    syl2and
end
