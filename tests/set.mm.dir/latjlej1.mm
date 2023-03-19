include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "latlej1.mm"
include "3adant3r1.mm"
include "wi.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "latjcl.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpan2d.mm"
include "latlej2.mm"
include "jctird.mm"
include "wb.mm"
include "simpr3.mm"
include "3jca.mm"
include "latjle12.mm"
include "syldan.mm"
include "sylibd.mm"

theorem latjlej1
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latlej.b: |- B = ( Base ` K )
  assume latlej.l: |- .<_ = ( le ` K )
  assume latlej.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ Y -> ( X .\/ Z ) .<_ ( Y .\/ Z ) ) )

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
    cZ
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    cZ
    c.or
    co
    #
    c.le
    wbr
    #
    cZ
    @7
    c.le
    wbr
    #
    wa
    #
    cX
    cZ
    c.or
    co
    @7
    c.le
    wbr
    #
    @5
    @6
    @8
    @9
    @5
    @6
    cY
    @7
    c.le
    wbr
    #
    @8
    @0
    @2
    @3
    @12
    @1
    cB
    c.or
    cK
    c.le
    cY
    cZ
    latlej.b
    latlej.l
    latlej.j
    latlej1
    3adant3r1
    @5
    @0
    @1
    @2
    @7
    cB
    wcel
    #
    @6
    @12
    wa
    @8
    wi
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    @0
    @2
    @3
    @13
    @1
    cB
    c.or
    cK
    cY
    cZ
    latlej.b
    latlej.j
    latjcl
    3adant3r1
    #
    cB
    cK
    c.le
    cX
    cY
    @7
    latlej.b
    latlej.l
    lattr
    syl13anc
    mpan2d
    @0
    @2
    @3
    @9
    @1
    cB
    c.or
    cK
    c.le
    cY
    cZ
    latlej.b
    latlej.l
    latlej.j
    latlej2
    3adant3r1
    jctird
    @0
    @4
    @1
    @3
    @13
    w3a
    @10
    @11
    wb
    @5
    @1
    @3
    @13
    @14
    @0
    @1
    @2
    @3
    simpr3
    @15
    3jca
    cB
    c.or
    cK
    c.le
    cX
    cZ
    @7
    latlej.b
    latlej.l
    latlej.j
    latjle12
    syldan
    sylibd
end
