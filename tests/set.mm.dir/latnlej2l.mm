include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "latnlej2.mm"
include "simpld.mm"

theorem latnlej2l
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ -. X .<_ ( Y .\/ Z ) ) -> -. X .<_ Y )

  proof
    cK
    clat
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cY
    cZ
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cX
    cY
    c.le
    wbr
    wn
    cX
    cZ
    c.le
    wbr
    wn
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
    latnlej2
    simpld
end
