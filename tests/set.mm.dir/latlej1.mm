include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "cop.mm"
include "cdm.mm"
include "cmee.mm"
include "cfv.mm"
include "eqid.mm"
include "latcl2.mm"
include "simpld.mm"
include "lejoin1.mm"

theorem latlej1
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume latlej.b: |- B = ( Base ` K )
  assume latlej.l: |- .<_ = ( le ` K )
  assume latlej.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> X .<_ ( X .\/ Y ) )

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
    c.or
    cK
    c.le
    clat
    cX
    cY
    latlej.b
    latlej.l
    latlej.j
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
    c.or
    cdm
    wcel
    @7
    cK
    cmee
    cfv
    #
    cdm
    wcel
    @3
    cB
    c.or
    cK
    @8
    cX
    cY
    latlej.b
    latlej.j
    @8
    eqid
    @4
    @5
    @6
    latcl2
    simpld
    lejoin1
end
