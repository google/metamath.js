include "cops.mm"
include "wcel.mm"
include "club.mm"
include "cfv.mm"
include "eqid.mm"
include "p1val.mm"
include "id.mm"
include "cdm.mm"
include "cglb.mm"
include "op01dm.mm"
include "simpld.mm"
include "lubcl.mm"
include "eqeltrd.mm"

theorem op1cl
  let cB: class B
  let c.1: class .1.
  let cK: class K
  assume op1cl.b: |- B = ( Base ` K )
  assume op1cl.u: |- .1. = ( 1. ` K )


  assert |- ( K e. OP -> .1. e. B )

  proof
    cK
    cops
    wcel
    #
    c.1
    cB
    cK
    club
    cfv
    #
    cfv
    cB
    cB
    @1
    c.1
    cK
    cops
    op1cl.b
    @1
    eqid
    #
    op1cl.u
    p1val
    @0
    cB
    cB
    @1
    cK
    cops
    op1cl.b
    @2
    @0
    id
    @0
    cB
    @1
    cdm
    wcel
    cB
    cK
    cglb
    cfv
    #
    cdm
    wcel
    cB
    @1
    @3
    cK
    op1cl.b
    @2
    @3
    eqid
    op01dm
    simpld
    lubcl
    eqeltrd
end
