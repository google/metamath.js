include "cal.mm"
include "wcel.mm"
include "wa.mm"
include "cglb.mm"
include "cfv.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "cdm.mm"
include "club.mm"
include "atl0dm.mm"
include "adantr.mm"
include "p0le.mm"

theorem atl0le
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume atl0le.b: |- B = ( Base ` K )
  assume atl0le.l: |- .<_ = ( le ` K )
  assume atl0le.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. AtLat /\ X e. B ) -> .0. .<_ X )

  proof
    cK
    cal
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
    cal
    cX
    c.0
    atl0le.b
    @2
    eqid
    #
    atl0le.l
    atl0le.z
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
    @1
    cB
    cK
    club
    cfv
    #
    @2
    cK
    atl0le.b
    @4
    eqid
    @3
    atl0dm
    adantr
    p0le
end
