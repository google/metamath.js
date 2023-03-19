include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "cglb.mm"
include "cfv.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "cdm.mm"
include "club.mm"
include "op01dm.mm"
include "simprd.mm"
include "adantr.mm"
include "p0le.mm"

theorem op0le
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume op0le.b: |- B = ( Base ` K )
  assume op0le.l: |- .<_ = ( le ` K )
  assume op0le.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> .0. .<_ X )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cB
    cK
    cglb
    cfv
    #
    cK
    c.le
    cops
    cX
    c.0
    op0le.b
    @2
    eqid
    #
    op0le.l
    op0le.z
    @0
    @1
    simpl
    @0
    @1
    simpr
    @0
    cB
    @2
    cdm
    wcel
    #
    @1
    @0
    cB
    cK
    club
    cfv
    #
    cdm
    wcel
    @4
    cB
    @5
    @2
    cK
    op0le.b
    @5
    eqid
    @3
    op01dm
    simprd
    adantr
    p0le
end
