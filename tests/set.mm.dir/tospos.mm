include "ctos.mm"
include "wcel.mm"
include "cpo.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wo.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "istos.mm"
include "simplbi.mm"

theorem tospos
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. Toset -> F e. Poset )

  proof
    cF
    ctos
    wcel
    cF
    cpo
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cF
    cple
    cfv
    #
    wbr
    @1
    @0
    @2
    wbr
    wo
    vy
    cF
    cbs
    cfv
    #
    wral
    vx
    @3
    wral
    vx
    vy
    @3
    cF
    @2
    @3
    eqid
    @2
    eqid
    istos
    simplbi
end
