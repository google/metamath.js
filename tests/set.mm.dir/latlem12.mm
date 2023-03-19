include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cpo.mm"
include "latpos.mm"
include "adantr.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simpr1.mm"
include "cop.mm"
include "cjn.mm"
include "cfv.mm"
include "cdm.mm"
include "eqid.mm"
include "simpl.mm"
include "latcl2.mm"
include "simprd.mm"
include "meetle.mm"

theorem latlem12
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


  assert |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .<_ Y /\ X .<_ Z ) <-> X .<_ ( Y ./\ Z ) ) )

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
    cK
    c.le
    c.an
    cY
    cZ
    cX
    latmle.b
    latmle.l
    latmle.m
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
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    @0
    @1
    @2
    @3
    simpr1
    @5
    cY
    cZ
    cop
    #
    cK
    cjn
    cfv
    #
    cdm
    wcel
    @8
    c.an
    cdm
    wcel
    @5
    cB
    @9
    cK
    c.an
    cY
    cZ
    latmle.b
    @9
    eqid
    latmle.m
    @0
    @4
    simpl
    @6
    @7
    latcl2
    simprd
    meetle
end
