include "cdlat.mm"
include "wcel.mm"
include "clat.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isdlat.mm"
include "simplbi.mm"

theorem dlatl
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( K e. DLat -> K e. Lat )

  proof
    cK
    cdlat
    wcel
    cK
    clat
    wcel
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cK
    cjn
    cfv
    #
    co
    cK
    cmee
    cfv
    #
    co
    @0
    @1
    @4
    co
    @0
    @2
    @4
    co
    @3
    co
    wceq
    vz
    cK
    cbs
    cfv
    #
    wral
    vy
    @5
    wral
    vx
    @5
    wral
    vx
    vy
    vz
    @5
    @3
    cK
    @4
    @5
    eqid
    @3
    eqid
    @4
    eqid
    isdlat
    simplbi
end
