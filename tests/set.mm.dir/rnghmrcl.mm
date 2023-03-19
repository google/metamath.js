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
include "elmpt2cl.mm"

theorem rnghmrcl
  let cR: class R
  let cS: class S
  let cF: class F
  let vr: setvar r
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( F e. ( R RngHomo S ) -> ( R e. Rng /\ S e. Rng ) )

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
    vw
    vs
    cv
    #
    cbs
    cfv
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
    @2
    @4
    cfv
    #
    @3
    @4
    cfv
    #
    @1
    cplusg
    cfv
    co
    wceq
    @2
    @3
    @0
    cmulr
    cfv
    co
    @4
    cfv
    @5
    @6
    @1
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
    @7
    wral
    vf
    vw
    cv
    @7
    cmap
    co
    crab
    csb
    csb
    cR
    cS
    crngh
    cF
    vx
    vy
    vw
    vv
    vf
    vs
    vr
    df-rnghomo
    elmpt2cl
end
