include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cpo.mm"
include "latpos.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "cop.mm"
include "cdm.mm"
include "cmee.mm"
include "cfv.mm"
include "eqid.mm"
include "simpl.mm"
include "latcl2.mm"
include "simpld.mm"
include "joinle.mm"

theorem latjle12
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .<_ Z /\ Y .<_ Z ) <-> ( X .\/ Y ) .<_ Z ) )

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
    #
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
    @0
    cK
    cpo
    wcel
    @4
    cK
    latpos
    adantr
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    @5
    cX
    cY
    cop
    #
    c.or
    cdm
    wcel
    @8
    cK
    cmee
    cfv
    #
    cdm
    wcel
    @5
    cB
    c.or
    cK
    @9
    cX
    cY
    latlej.b
    latlej.j
    @9
    eqid
    @0
    @4
    simpl
    @6
    @7
    latcl2
    simpld
    joinle
end
