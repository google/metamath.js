include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "simpl.mm"
include "latmcl.mm"
include "3adant3r3.mm"
include "simpr1.mm"
include "latjcl.mm"
include "3adant3r2.mm"
include "wbr.mm"
include "latmle1.mm"
include "latlej1.mm"
include "lattrd.mm"

theorem latmlej11
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X ./\ Y ) .<_ ( X .\/ Z ) )

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
    cB
    cK
    c.le
    cX
    cY
    c.an
    co
    #
    cX
    cX
    cZ
    c.or
    co
    #
    latledi.b
    latledi.l
    @0
    @4
    simpl
    @0
    @1
    @2
    @5
    cB
    wcel
    @3
    cB
    cK
    c.an
    cX
    cY
    latledi.b
    latledi.m
    latmcl
    3adant3r3
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @3
    @6
    cB
    wcel
    @2
    cB
    c.or
    cK
    cX
    cZ
    latledi.b
    latledi.j
    latjcl
    3adant3r2
    @0
    @1
    @2
    @5
    cX
    c.le
    wbr
    @3
    cB
    cK
    c.le
    c.an
    cX
    cY
    latledi.b
    latledi.l
    latledi.m
    latmle1
    3adant3r3
    @0
    @1
    @3
    cX
    @6
    c.le
    wbr
    @2
    cB
    c.or
    cK
    c.le
    cX
    cZ
    latledi.b
    latledi.l
    latledi.j
    latlej1
    3adant3r2
    lattrd
end
