include "cablo.mm"
include "wcel.mm"
include "cgr.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crn.mm"
include "wral.mm"
include "eqid.mm"
include "isablo.mm"
include "simplbi.mm"

theorem ablogrpo
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( G e. AbelOp -> G e. GrpOp )

  proof
    cG
    cablo
    wcel
    cG
    cgr
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    @1
    @0
    cG
    co
    wceq
    vy
    cG
    crn
    #
    wral
    vx
    @2
    wral
    vx
    vy
    cG
    @2
    @2
    eqid
    isablo
    simplbi
end
