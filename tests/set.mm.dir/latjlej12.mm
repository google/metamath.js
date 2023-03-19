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
include "latjlej1.mm"
include "syl13anc.mm"
include "simp3r.mm"
include "latjlej2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lattr.mm"
include "syl2and.mm"

theorem latjlej12
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latlej.b: |- B = ( Base ` K )
  assume latlej.l: |- .<_ = ( le ` K )
  assume latlej.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B ) /\ ( Z e. B /\ W e. B ) ) -> ( ( X .<_ Y /\ Z .<_ W ) -> ( X .\/ Z ) .<_ ( Y .\/ W ) ) )

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
    c.or
    co
    #
    cY
    cZ
    c.or
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
    c.or
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
    c.or
    cK
    c.le
    cX
    cY
    cZ
    latlej.b
    latlej.l
    latlej.j
    latjlej1
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
    c.or
    cK
    c.le
    cZ
    cW
    cY
    latlej.b
    latlej.l
    latlej.j
    latjlej2
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
    c.or
    cK
    cX
    cZ
    latlej.b
    latlej.j
    latjcl
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
    c.or
    cK
    cY
    cZ
    latlej.b
    latlej.j
    latjcl
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
    c.or
    cK
    cY
    cW
    latlej.b
    latlej.j
    latjcl
    syl3anc
    cB
    cK
    c.le
    @9
    @10
    @13
    latlej.b
    latlej.l
    lattr
    syl13anc
    syl2and
end
