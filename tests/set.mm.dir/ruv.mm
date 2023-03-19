include "cvv.mm"
include "weq.mm"
include "cab.mm"
include "cv.mm"
include "wnel.mm"
include "df-v.mm"
include "equid.mm"
include "elirrv.mm"
include "nelir.mm"
include "2th.mm"
include "abbii.mm"
include "eqtr2i.mm"

theorem ruv
  let vx: setvar x


  assert |- { x | x e/ x } = _V

  proof
    cvv
    vx
    vx
    weq
    #
    vx
    cab
    vx
    cv
    #
    @1
    wnel
    #
    vx
    cab
    vx
    df-v
    @0
    @2
    vx
    @0
    @2
    vx
    equid
    @1
    @1
    vx
    elirrv
    nelir
    2th
    abbii
    eqtr2i
end
