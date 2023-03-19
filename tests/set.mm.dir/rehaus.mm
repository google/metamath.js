include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cha.mm"
include "eqid.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "methaus.mm"
include "ax-mp.mm"

theorem rehaus
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( topGen ` ran (,) ) e. Haus

  proof
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cr
    cxmt
    cfv
    wcel
    cioo
    crn
    ctg
    cfv
    #
    cha
    wcel
    @0
    @0
    eqid
    #
    rexmet
    @0
    @1
    cr
    @0
    @0
    cmopn
    cfv
    #
    @2
    @3
    eqid
    tgioo
    methaus
    ax-mp
end
