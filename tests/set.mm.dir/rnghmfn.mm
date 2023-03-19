include "crng.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "cmulr.mm"
include "wa.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "csb.mm"
include "crngh.mm"
include "df-rnghomo.mm"
include "ovex.mm"
include "rabex.mm"
include "csbex.mm"
include "fnmpt2i.mm"

theorem rnghmfn
  let vr: setvar r
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- RngHomo Fn ( Rng X. Rng )

  proof
    vr
    vs
    crng
    crng
    vv
    vr
    cv
    #
    cbs
    cfv
    #
    vw
    vs
    cv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    cplusg
    cfv
    co
    vf
    cv
    #
    cfv
    @4
    @6
    cfv
    #
    @5
    @6
    cfv
    #
    @2
    cplusg
    cfv
    co
    wceq
    @4
    @5
    @0
    cmulr
    cfv
    co
    @6
    cfv
    @7
    @8
    @2
    cmulr
    cfv
    co
    wceq
    wa
    vy
    vv
    cv
    #
    wral
    vx
    @9
    wral
    #
    vf
    vw
    cv
    #
    @9
    cmap
    co
    #
    crab
    #
    csb
    #
    csb
    crngh
    vx
    vy
    vw
    vv
    vf
    vs
    vr
    df-rnghomo
    vv
    @1
    @14
    vw
    @3
    @13
    @10
    vf
    @12
    @11
    @9
    cmap
    ovex
    rabex
    csbex
    csbex
    fnmpt2i
end
