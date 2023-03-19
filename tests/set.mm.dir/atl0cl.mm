include "cal.mm"
include "wcel.mm"
include "cglb.mm"
include "cfv.mm"
include "eqid.mm"
include "p0val.mm"
include "id.mm"
include "club.mm"
include "atl0dm.mm"
include "glbcl.mm"
include "eqeltrd.mm"

theorem atl0cl
  let cB: class B
  let cK: class K
  let c.0: class .0.
  assume atl0cl.b: |- B = ( Base ` K )
  assume atl0cl.z: |- .0. = ( 0. ` K )


  assert |- ( K e. AtLat -> .0. e. B )

  proof
    cK
    cal
    wcel
    #
    c.0
    cB
    cK
    cglb
    cfv
    #
    cfv
    cB
    cB
    @1
    cK
    cal
    c.0
    atl0cl.b
    @1
    eqid
    #
    atl0cl.z
    p0val
    @0
    cB
    cB
    @1
    cK
    cal
    atl0cl.b
    @2
    @0
    id
    cB
    cK
    club
    cfv
    #
    @1
    cK
    atl0cl.b
    @3
    eqid
    @2
    atl0dm
    glbcl
    eqeltrd
end
