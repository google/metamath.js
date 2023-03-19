include "cops.mm"
include "wcel.mm"
include "cglb.mm"
include "cfv.mm"
include "eqid.mm"
include "p0val.mm"
include "id.mm"
include "club.mm"
include "cdm.mm"
include "op01dm.mm"
include "simprd.mm"
include "glbcl.mm"
include "eqeltrd.mm"

theorem op0cl
  let cB: class B
  let cK: class K
  let c.0: class .0.
  assume op0cl.b: |- B = ( Base ` K )
  assume op0cl.z: |- .0. = ( 0. ` K )


  assert |- ( K e. OP -> .0. e. B )

  proof
    cK
    cops
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
    cops
    c.0
    op0cl.b
    @1
    eqid
    #
    op0cl.z
    p0val
    @0
    cB
    cB
    @1
    cK
    cops
    op0cl.b
    @2
    @0
    id
    @0
    cB
    cK
    club
    cfv
    #
    cdm
    wcel
    cB
    @1
    cdm
    wcel
    cB
    @3
    @1
    cK
    op0cl.b
    @3
    eqid
    @2
    op01dm
    simprd
    glbcl
    eqeltrd
end
