include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "latmlem1.mm"
include "wceq.mm"
include "latmcom.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "breq12d.mm"
include "sylibd.mm"

theorem latmlem2
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume latmle.b: |- B = ( Base ` K )
  assume latmle.l: |- .<_ = ( le ` K )
  assume latmle.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .<_ Y -> ( Z ./\ X ) .<_ ( Z ./\ Y ) ) )

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
    c.an
    co
    #
    cY
    cZ
    c.an
    co
    #
    c.le
    wbr
    cZ
    cX
    c.an
    co
    #
    cZ
    cY
    c.an
    co
    #
    c.le
    wbr
    cB
    cK
    c.le
    c.an
    cX
    cY
    cZ
    latmle.b
    latmle.l
    latmle.m
    latmlem1
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
    cK
    c.an
    cX
    cZ
    latmle.b
    latmle.m
    latmcom
    3adant3r2
    @0
    @2
    @3
    @6
    @8
    wceq
    @1
    cB
    cK
    c.an
    cY
    cZ
    latmle.b
    latmle.m
    latmcom
    3adant3r1
    breq12d
    sylibd
end
