include "cc.mm"
include "csin.mm"
include "cdv.mm"
include "co.mm"
include "ccos.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "dvsincos.mm"
include "simpri.mm"

theorem dvcos
  let vx: setvar x


  assert |- ( CC _D cos ) = ( x e. CC |-> -u ( sin ` x ) )

  proof
    cc
    csin
    cdv
    co
    ccos
    wceq
    cc
    ccos
    cdv
    co
    vx
    cc
    vx
    cv
    csin
    cfv
    cneg
    cmpt
    wceq
    vx
    dvsincos
    simpri
end
