include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "latmlej11.mm"
include "wceq.mm"
include "latjcom.mm"
include "3adant3r2.mm"
include "breqtrd.mm"

theorem latmlej12
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X ./\ Y ) .<_ ( Z .\/ X ) )

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
    cX
    cZ
    c.or
    co
    #
    cZ
    cX
    c.or
    co
    #
    c.le
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
    @0
    @1
    @3
    @4
    @5
    wceq
    @2
    cB
    c.or
    cK
    cX
    cZ
    latledi.b
    latledi.j
    latjcom
    3adant3r2
    breqtrd
end
