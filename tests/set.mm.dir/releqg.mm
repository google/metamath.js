include "wrel.mm"
include "cqg.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cminusg.mm"
include "cplusg.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "df-eqg.mm"
include "relmpt2opab.mm"
include "releqi.mm"
include "mpbir.mm"

theorem releqg
  let cR: class R
  let cS: class S
  let cG: class G
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume releqg.r: |- R = ( G ~QG S )


  assert |- Rel R

  proof
    cR
    wrel
    cG
    cS
    cqg
    co
    #
    wrel
    vx
    cv
    #
    vy
    cv
    #
    cpr
    vg
    cv
    #
    cbs
    cfv
    wss
    @1
    @3
    cminusg
    cfv
    cfv
    @2
    @3
    cplusg
    cfv
    co
    vs
    cv
    wcel
    wa
    vg
    vs
    vx
    vy
    cvv
    cvv
    cG
    cS
    cqg
    vx
    vy
    vs
    vg
    df-eqg
    relmpt2opab
    cR
    @0
    releqg.r
    releqi
    mpbir
end
