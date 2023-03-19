include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "latjlej1.mm"
include "wceq.mm"
include "latjcom.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "breq12d.mm"
include "sylibd.mm"

theorem latjlej2
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ Y -> ( Z .\/ X ) .<_ ( Z .\/ Y ) ) )

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
    wa
    #
    cX
    cY
    c.le
    wbr
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
    cZ
    cX
    c.or
    co
    #
    cZ
    cY
    c.or
    co
    #
    c.le
    wbr
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
    @4
    @5
    @7
    @6
    @8
    c.le
    @0
    @1
    @3
    @5
    @7
    wceq
    @2
    cB
    c.or
    cK
    cX
    cZ
    latlej.b
    latlej.j
    latjcom
    3adant3r2
    @0
    @2
    @3
    @6
    @8
    wceq
    @1
    cB
    c.or
    cK
    cY
    cZ
    latlej.b
    latlej.j
    latjcom
    3adant3r1
    breq12d
    sylibd
end
