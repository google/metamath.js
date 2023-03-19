include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "latlej1.mm"
include "3adant3r1.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "latlej2.mm"
include "jcad.mm"
include "3impia.mm"

theorem latnlej
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ -. X .<_ ( Y .\/ Z ) ) -> ( X =/= Y /\ X =/= Z ) )

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
    wne
    #
    cX
    cZ
    wne
    #
    wa
    @0
    @4
    wa
    #
    @7
    @8
    @9
    @10
    @6
    cX
    cY
    @10
    @6
    cX
    cY
    wceq
    cY
    @5
    c.le
    wbr
    #
    @0
    @2
    @3
    @11
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
    cX
    cY
    @5
    c.le
    breq1
    syl5ibrcom
    necon3bd
    @10
    @6
    cX
    cZ
    @10
    @6
    cX
    cZ
    wceq
    cZ
    @5
    c.le
    wbr
    #
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
    latlej2
    3adant3r1
    cX
    cZ
    @5
    c.le
    breq1
    syl5ibrcom
    necon3bd
    jcad
    3impia
end
