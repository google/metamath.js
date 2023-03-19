include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "latmcom.mm"
include "3adant3r3.mm"
include "latmlej11.mm"
include "eqbrtrrd.mm"

theorem latmlej21
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latledi.b: |- B = ( Base ` K )
  assume latledi.l: |- .<_ = ( le ` K )
  assume latledi.j: |- .\/ = ( join ` K )
  assume latledi.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( Y ./\ X ) .<_ ( X .\/ Z ) )

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
    cX
    cY
    c.an
    co
    #
    cY
    cX
    c.an
    co
    #
    cX
    cZ
    c.or
    co
    c.le
    @0
    @1
    @2
    @4
    @5
    wceq
    @3
    cB
    cK
    c.an
    cX
    cY
    latledi.b
    latledi.m
    latmcom
    3adant3r3
    cB
    c.or
    cK
    c.le
    c.an
    cX
    cY
    cZ
    latledi.b
    latledi.l
    latledi.j
    latledi.m
    latmlej11
    eqbrtrrd
end
