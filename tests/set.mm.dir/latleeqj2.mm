include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "latleeqj1.mm"
include "latjcom.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem latleeqj2
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume latlej.b: |- B = ( Base ` K )
  assume latlej.l: |- .<_ = ( le ` K )
  assume latlej.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> ( Y .\/ X ) = Y ) )

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
    w3a
    #
    cX
    cY
    c.le
    wbr
    cX
    cY
    c.or
    co
    #
    cY
    wceq
    cY
    cX
    c.or
    co
    #
    cY
    wceq
    cB
    c.or
    cK
    c.le
    cX
    cY
    latlej.b
    latlej.l
    latlej.j
    latleeqj1
    @0
    @1
    @2
    cY
    cB
    c.or
    cK
    cX
    cY
    latlej.b
    latlej.j
    latjcom
    eqeq1d
    bitrd
end
