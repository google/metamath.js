include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "crng.mm"
include "wa.mm"
include "cghm.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isrnghm.mm"
include "simprl.mm"
include "sylbi.mm"

theorem rnghmghm
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( F e. ( R RngHomo S ) -> F e. ( R GrpHom S ) )

  proof
    cF
    cR
    cS
    crngh
    co
    wcel
    cR
    crng
    wcel
    cS
    crng
    wcel
    wa
    #
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    cF
    cfv
    @2
    cF
    cfv
    @3
    cF
    cfv
    cS
    cmulr
    cfv
    #
    co
    wceq
    vy
    cR
    cbs
    cfv
    #
    wral
    vx
    @6
    wral
    #
    wa
    wa
    @1
    vx
    vy
    @6
    cR
    cS
    @4
    cF
    @5
    @6
    eqid
    @4
    eqid
    @5
    eqid
    isrnghm
    @0
    @1
    @7
    simprl
    sylbi
end
