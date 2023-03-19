include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
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
include "con3d.mm"
include "latlej2.mm"
include "simpr3.mm"
include "jcad.mm"
include "3impia.mm"

theorem latnlej2
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ -. X .<_ ( Y .\/ Z ) ) -> ( -. X .<_ Y /\ -. X .<_ Z ) )

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
    cX
    cY
    cZ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cX
    cY
    c.le
    wbr
    #
    wn
    #
    cX
    cZ
    c.le
    wbr
    #
    wn
    #
    wa
    @0
    @4
    wa
    #
    @7
    @9
    @11
    @12
    @8
    @6
    @12
    @8
    cY
    @5
    c.le
    wbr
    #
    @6
    @0
    @2
    @3
    @13
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
    @12
    @0
    @1
    @2
    @5
    cB
    wcel
    #
    @8
    @13
    wa
    @6
    wi
    @0
    @4
    simpl
    #
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
    @14
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
    @5
    latlej.b
    latlej.l
    lattr
    syl13anc
    mpan2d
    con3d
    @12
    @10
    @6
    @12
    @10
    cZ
    @5
    c.le
    wbr
    #
    @6
    @0
    @2
    @3
    @18
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
    @12
    @0
    @1
    @3
    @14
    @10
    @18
    wa
    @6
    wi
    @15
    @16
    @0
    @1
    @2
    @3
    simpr3
    @17
    cB
    cK
    c.le
    cX
    cZ
    @5
    latlej.b
    latlej.l
    lattr
    syl13anc
    mpan2d
    con3d
    jcad
    3impia
end
