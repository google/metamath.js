include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "latleeqm1.mm"
include "latmcom.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem latleeqm2
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latmle.b: |- B = ( Base ` K )
  assume latmle.l: |- .<_ = ( le ` K )
  assume latmle.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> ( Y ./\ X ) = X ) )

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
    c.an
    co
    #
    cX
    wceq
    cY
    cX
    c.an
    co
    #
    cX
    wceq
    cB
    cK
    c.le
    c.an
    cX
    cY
    latmle.b
    latmle.l
    latmle.m
    latleeqm1
    @0
    @1
    @2
    cX
    cB
    cK
    c.an
    cX
    cY
    latmle.b
    latmle.m
    latmcom
    eqeq1d
    bitrd
end
