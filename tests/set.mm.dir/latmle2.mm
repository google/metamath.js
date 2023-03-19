include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "cop.mm"
include "cjn.mm"
include "cfv.mm"
include "cdm.mm"
include "eqid.mm"
include "latcl2.mm"
include "simprd.mm"
include "lemeet2.mm"

theorem latmle2
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latmle.b: |- B = ( Base ` K )
  assume latmle.l: |- .<_ = ( le ` K )
  assume latmle.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X ./\ Y ) .<_ Y )

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
    w3a
    #
    cB
    cK
    c.le
    c.an
    clat
    cX
    cY
    latmle.b
    latmle.l
    latmle.m
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    @3
    cX
    cY
    cop
    #
    cK
    cjn
    cfv
    #
    cdm
    wcel
    @7
    c.an
    cdm
    wcel
    @3
    cB
    @8
    cK
    c.an
    cX
    cY
    latmle.b
    @8
    eqid
    latmle.m
    @4
    @5
    @6
    latcl2
    simprd
    lemeet2
end
