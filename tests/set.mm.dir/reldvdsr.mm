include "wrel.mm"
include "cdsr.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "wcel.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cvv.mm"
include "df-dvdsr.mm"
include "relmptopab.mm"
include "releqi.mm"
include "mpbir.mm"

theorem reldvdsr
  let c.pa: class .||
  let cR: class R
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume reldvdsr.1: |- .|| = ( ||r ` R )


  assert |- Rel .||

  proof
    c.pa
    wrel
    cR
    cdsr
    cfv
    #
    wrel
    vx
    cv
    #
    vw
    cv
    #
    cbs
    cfv
    #
    wcel
    vz
    cv
    @1
    @2
    cmulr
    cfv
    co
    vy
    cv
    wceq
    vz
    @3
    wrex
    wa
    vw
    vx
    vy
    cvv
    cR
    cdsr
    vx
    vy
    vz
    vw
    df-dvdsr
    relmptopab
    c.pa
    @0
    reldvdsr.1
    releqi
    mpbir
end
