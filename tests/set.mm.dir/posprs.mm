include "cpo.mm"
include "wcel.mm"
include "cpreset.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "ispos2.mm"
include "simplbi.mm"

theorem posprs
  let cK: class K
  let vx: setvar x
  let vy: setvar y


  assert |- ( K e. Poset -> K e. Preset )

  proof
    cK
    cpo
    wcel
    cK
    cpreset
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    @1
    @0
    @2
    wbr
    wa
    vx
    vy
    weq
    wi
    vy
    cK
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
    cK
    @2
    @3
    eqid
    @2
    eqid
    ispos2
    simplbi
end
